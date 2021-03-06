/*
 * Copyright 2010-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license
 * that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.fir.resolve.calls

import org.jetbrains.kotlin.fir.expressions.*
import org.jetbrains.kotlin.fir.types.ConeIntegerLiteralType
import org.jetbrains.kotlin.fir.returnExpressions
import org.jetbrains.kotlin.fir.types.ConeKotlinType
import org.jetbrains.kotlin.fir.types.ConeTypeVariable
import org.jetbrains.kotlin.fir.types.FirTypeRef
import org.jetbrains.kotlin.resolve.calls.inference.components.KotlinConstraintSystemCompleter
import org.jetbrains.kotlin.resolve.calls.inference.components.TypeVariableDirectionCalculator
import org.jetbrains.kotlin.resolve.calls.inference.components.VariableFixationFinder
import org.jetbrains.kotlin.resolve.calls.inference.model.VariableWithConstraints
import org.jetbrains.kotlin.resolve.calls.model.PostponedResolvedAtom
import org.jetbrains.kotlin.resolve.calls.model.PostponedResolvedAtomMarker
import org.jetbrains.kotlin.types.model.KotlinTypeMarker
import org.jetbrains.kotlin.types.model.TypeConstructorMarker
import org.jetbrains.kotlin.types.model.isIntegerLiteralTypeConstructor
import org.jetbrains.kotlin.types.model.typeConstructor
import org.jetbrains.kotlin.utils.addIfNotNull
import org.jetbrains.kotlin.utils.addToStdlib.safeAs


fun Candidate.computeCompletionMode(
    components: InferenceComponents,
    expectedType: FirTypeRef?,
    currentReturnType: ConeKotlinType?
): KotlinConstraintSystemCompleter.ConstraintSystemCompletionMode {
    // Presence of expected type means that we trying to complete outermost call => completion mode should be full
    if (expectedType != null) return KotlinConstraintSystemCompleter.ConstraintSystemCompletionMode.FULL

    // This is questionable as null return type can be only for error call
    if (currentReturnType == null || currentReturnType is ConeIntegerLiteralType)
        return KotlinConstraintSystemCompleter.ConstraintSystemCompletionMode.PARTIAL

    return when {
        // Consider call foo(bar(x)), if return type of bar is a proper one, then we can complete resolve for bar => full completion mode
        // Otherwise, we shouldn't complete bar until we process call foo
        csBuilder.isProperType(currentReturnType) -> KotlinConstraintSystemCompleter.ConstraintSystemCompletionMode.FULL

        // Nested call is connected with the outer one through the UPPER constraint (returnType <: expectedOuterType)
        // This means that there will be no new LOWER constraints =>
        //   it's possible to complete call now if there are proper LOWER constraints
        csBuilder.isTypeVariable(currentReturnType) ->
            if (hasProperNonTrivialLowerConstraints(components, currentReturnType))
                KotlinConstraintSystemCompleter.ConstraintSystemCompletionMode.FULL
            else
                KotlinConstraintSystemCompleter.ConstraintSystemCompletionMode.PARTIAL

        // Return type has proper equal constraints => there is no need in the outer call
        containsTypeVariablesWithProperEqualConstraints(components, currentReturnType) -> KotlinConstraintSystemCompleter.ConstraintSystemCompletionMode.FULL

        else -> KotlinConstraintSystemCompleter.ConstraintSystemCompletionMode.PARTIAL
    }
}

val Candidate.csBuilder get() = system.getBuilder()

private fun Candidate.containsTypeVariablesWithProperEqualConstraints(components: InferenceComponents, type: ConeKotlinType): Boolean =
    with(components.ctx){
        for ((variableConstructor, variableWithConstraints) in csBuilder.currentStorage().notFixedTypeVariables) {
            if (!type.contains { it.typeConstructor() == variableConstructor }) continue

            val constraints = variableWithConstraints.constraints
            val onlyProperEqualConstraints =
                constraints.isNotEmpty() && constraints.any { it.kind.isEqual() && csBuilder.isProperType(it.type) }

            if (!onlyProperEqualConstraints) return false
        }

        return true
    }

private fun Candidate.hasProperNonTrivialLowerConstraints(components: InferenceComponents, typeVariable: ConeKotlinType): Boolean {
    assert(csBuilder.isTypeVariable(typeVariable)) { "$typeVariable is not a type variable" }

    val context = components.ctx
    val constructor = typeVariable.typeConstructor(context)
    val variableWithConstraints = csBuilder.currentStorage().notFixedTypeVariables[constructor] ?: return false
    val constraints = variableWithConstraints.constraints
    // TODO: support Exact annotation
    // see KotlinCallCompleter:244
    return constraints.isNotEmpty() && constraints.any {
        !it.type.typeConstructor(context).isIntegerLiteralTypeConstructor(context) &&
                (it.kind.isLower() || it.kind.isEqual()) && csBuilder.isProperType(it.type)
    }

}


class ConstraintSystemCompleter(val components: InferenceComponents) {
    private val variableFixationFinder = VariableFixationFinder(components.trivialConstraintTypeInferenceOracle)
    fun complete(
        c: KotlinConstraintSystemCompleter.Context,
        completionMode: KotlinConstraintSystemCompleter.ConstraintSystemCompletionMode,
        topLevelAtoms: List<FirStatement>,
        candidateReturnType: ConeKotlinType,
        analyze: (PostponedResolvedAtomMarker) -> Unit
    ) {

        while (true) {
            if (analyzePostponeArgumentIfPossible(c, topLevelAtoms, analyze)) continue

            val allTypeVariables = getOrderedAllTypeVariables(c, topLevelAtoms)
            val postponedKtPrimitives = getOrderedNotAnalyzedPostponedArguments(topLevelAtoms)
            val variableForFixation =
                variableFixationFinder.findFirstVariableForFixation(
                    c, allTypeVariables, postponedKtPrimitives, completionMode, candidateReturnType
                ) ?: break

//            if (shouldForceCallableReferenceOrLambdaResolution(completionMode, variableForFixation)) {
//                if (forcePostponedAtomResolution<ResolvedCallableReferenceAtom>(topLevelAtoms, analyze)) continue
//                if (forcePostponedAtomResolution<LambdaWithTypeVariableAsExpectedTypeAtom>(topLevelAtoms, analyze)) continue
//            }

            if (variableForFixation.hasProperConstraint || completionMode == KotlinConstraintSystemCompleter.ConstraintSystemCompletionMode.FULL) {
                val variableWithConstraints = c.notFixedTypeVariables.getValue(variableForFixation.variable)

                fixVariable(c, candidateReturnType, variableWithConstraints, emptyList())

//                if (!variableForFixation.hasProperConstraint) {
//                    c.addError(NotEnoughInformationForTypeParameter(variableWithConstraints.typeVariable))
//                }
                continue
            }

            break
        }

        if (completionMode == KotlinConstraintSystemCompleter.ConstraintSystemCompletionMode.FULL) {
            // force resolution for all not-analyzed argument's
            getOrderedNotAnalyzedPostponedArguments(topLevelAtoms).forEach(analyze)
//
//            if (c.notFixedTypeVariables.isNotEmpty() && c.postponedTypeVariables.isEmpty()) {
//                runCompletion(c, completionMode, topLevelAtoms, topLevelType, analyze)
//            }
        }
    }

    private fun getOrderedAllTypeVariables(
        c: KotlinConstraintSystemCompleter.Context,
        topLevelAtoms: List<FirStatement>
    ): List<TypeConstructorMarker> {
        val result = LinkedHashSet<TypeConstructorMarker>(c.notFixedTypeVariables.size)
        fun ConeTypeVariable?.toTypeConstructor(): TypeConstructorMarker? =
            this?.typeConstructor?.takeIf { it in c.notFixedTypeVariables.keys }

        fun FirStatement.collectAllTypeVariables() {
            this.processAllContainingCallCandidates(processBlocks = true) { candidate ->
                candidate.freshVariables.mapNotNullTo(result) { typeVariable ->
                    typeVariable.toTypeConstructor()
                }

                for (lambdaAtom in candidate.postponedAtoms.filterIsInstance<ResolvedLambdaAtom>()) {
                    result.addIfNotNull(lambdaAtom.typeVariableForLambdaReturnType.toTypeConstructor())
                    if (lambdaAtom.analyzed) {
                        for (firStatement in lambdaAtom.returnStatements) {
                            firStatement.collectAllTypeVariables()
                        }
                    }
                }
            }
        }

        for (topLevel in topLevelAtoms) {
            topLevel.collectAllTypeVariables()
        }

        require(result.size == c.notFixedTypeVariables.size) {
            val notFoundTypeVariables = c.notFixedTypeVariables.keys.toMutableSet().apply { removeAll(result) }
            "Not all type variables found: $notFoundTypeVariables"
        }

        return result.toList()
    }

    private fun fixVariable(
        c: KotlinConstraintSystemCompleter.Context,
        topLevelType: KotlinTypeMarker,
        variableWithConstraints: VariableWithConstraints,
        postponedResolveKtPrimitives: List<PostponedResolvedAtom>
    ) {
        val direction = TypeVariableDirectionCalculator(c, postponedResolveKtPrimitives, topLevelType).getDirection(variableWithConstraints)
        fixVariable(c, variableWithConstraints, direction)
    }

    fun fixVariable(
        c: KotlinConstraintSystemCompleter.Context,
        variableWithConstraints: VariableWithConstraints,
        direction: TypeVariableDirectionCalculator.ResolveDirection
    ) {
        val resultType = components.resultTypeResolver.findResultType(c, variableWithConstraints, direction)
        c.fixVariable(variableWithConstraints.typeVariable, resultType, atom = null) // TODO: obtain atom for diagnostics
    }

    private fun analyzePostponeArgumentIfPossible(
        c: KotlinConstraintSystemCompleter.Context,
        topLevelAtoms: List<FirStatement>,
        analyze: (PostponedResolvedAtomMarker) -> Unit
    ): Boolean {
        for (argument in getOrderedNotAnalyzedPostponedArguments(topLevelAtoms)) {
            if (canWeAnalyzeIt(c, argument)) {
                analyze(argument)
                return true
            }
        }
        return false
    }

    private fun getOrderedNotAnalyzedPostponedArguments(topLevelAtoms: List<FirStatement>): List<PostponedResolvedAtomMarker> {
        val notAnalyzedArguments = arrayListOf<PostponedResolvedAtomMarker>()
        for (primitive in topLevelAtoms) {
            primitive.processAllContainingCallCandidates(
                // TODO: remove this argument and relevant parameter
                // Currently, it's used because otherwise problem happens with a lambda in a try-block (see tryWithLambdaInside test)
                processBlocks = primitive !is FirTryExpression
            ) { candidate ->
                candidate.postponedAtoms.forEach {
                    notAnalyzedArguments.addIfNotNull(it.safeAs<PostponedResolvedAtomMarker>()?.takeUnless { it.analyzed })
                }
            }
        }

        return notAnalyzedArguments
    }

    private fun FirStatement.processAllContainingCallCandidates(processBlocks: Boolean, processor: (Candidate) -> Unit) {
        when (this) {
            is FirFunctionCall -> {
                processCandidateIfApplicable(processor)
                this.arguments.forEach { it.processAllContainingCallCandidates(processBlocks, processor) }
            }

            is FirWhenExpression -> {
                processCandidateIfApplicable(processor)
                this.branches.forEach { it.result.processAllContainingCallCandidates(processBlocks, processor) }
            }

            is FirTryExpression -> {
                processCandidateIfApplicable(processor)
                tryBlock.processAllContainingCallCandidates(processBlocks, processor)
                catches.forEach { it.block.processAllContainingCallCandidates(processBlocks, processor) }
            }

            is FirCheckNotNullCall -> {
                processCandidateIfApplicable(processor)
                this.arguments.forEach { it.processAllContainingCallCandidates(processBlocks, processor) }
            }

            is FirQualifiedAccessExpression -> {
                processCandidateIfApplicable(processor)
            }

            is FirVariableAssignment -> {
                processCandidateIfApplicable(processor)
                rValue.processAllContainingCallCandidates(processBlocks, processor)
            }

            is FirWrappedArgumentExpression -> this.expression.processAllContainingCallCandidates(processBlocks, processor)
            is FirBlock -> {
                if (processBlocks) {
                    this.returnExpressions().forEach { it.processAllContainingCallCandidates(processBlocks, processor) }
                }
            }

            is FirDelegatedConstructorCall -> {
                processCandidateIfApplicable(processor)
                this.arguments.forEach { it.processAllContainingCallCandidates(processBlocks, processor) }
            }
        }
    }

    private inline fun FirResolvable.processCandidateIfApplicable(processor: (Candidate) -> Unit) {
        (calleeReference as? FirNamedReferenceWithCandidate)?.candidate?.let(processor)
    }

    private fun canWeAnalyzeIt(c: KotlinConstraintSystemCompleter.Context, argument: PostponedResolvedAtomMarker): Boolean {
        if (argument.analyzed) return false

        return argument.inputTypes.all { c.containsOnlyFixedOrPostponedVariables(it) }
    }

}
