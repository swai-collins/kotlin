/*
 * Copyright 2010-2019 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.fir.resolve.calls

import org.jetbrains.kotlin.descriptors.ClassKind
import org.jetbrains.kotlin.fir.FirSession
import org.jetbrains.kotlin.fir.declarations.*
import org.jetbrains.kotlin.fir.declarations.impl.FirImportImpl
import org.jetbrains.kotlin.fir.declarations.impl.FirResolvedImportImpl
import org.jetbrains.kotlin.fir.expressions.FirExpression
import org.jetbrains.kotlin.fir.expressions.FirResolvedQualifier
import org.jetbrains.kotlin.fir.expressions.impl.FirQualifiedAccessExpressionImpl
import org.jetbrains.kotlin.fir.resolve.BodyResolveComponents
import org.jetbrains.kotlin.fir.resolve.calls.TowerDataKind.*
import org.jetbrains.kotlin.fir.resolve.transformQualifiedAccessUsingSmartcastInfo
import org.jetbrains.kotlin.fir.resolve.transformers.ReturnTypeCalculator
import org.jetbrains.kotlin.fir.resolve.transformers.body.resolve.firUnsafe
import org.jetbrains.kotlin.fir.scopes.FirScope
import org.jetbrains.kotlin.fir.scopes.ProcessorAction.NONE
import org.jetbrains.kotlin.fir.scopes.impl.FirExplicitSimpleImportingScope
import org.jetbrains.kotlin.fir.scopes.impl.FirLocalScope
import org.jetbrains.kotlin.fir.scopes.impl.FirStaticScope
import org.jetbrains.kotlin.fir.symbols.AbstractFirBasedSymbol
import org.jetbrains.kotlin.fir.symbols.impl.FirCallableSymbol
import org.jetbrains.kotlin.fir.symbols.impl.FirClassSymbol
import org.jetbrains.kotlin.fir.symbols.impl.FirVariableSymbol
import org.jetbrains.kotlin.fir.types.ConeIntegerLiteralType
import org.jetbrains.kotlin.fir.types.coneTypeSafe
import org.jetbrains.kotlin.fir.types.isExtensionFunctionType
import org.jetbrains.kotlin.name.FqName
import org.jetbrains.kotlin.resolve.calls.tasks.ExplicitReceiverKind
import org.jetbrains.kotlin.resolve.descriptorUtil.HIDES_MEMBERS_NAME_LIST
import org.jetbrains.kotlin.util.OperatorNameConventions
import java.util.*
import kotlin.coroutines.*

enum class TowerDataKind {
    EMPTY,       // Corresponds to stub tower level which is replaced by receiver-related level
    TOWER_LEVEL  // Corresponds to real tower level which may process elements itself
}

class FirTowerResolver(
    val typeCalculator: ReturnTypeCalculator,
    val components: BodyResolveComponents,
    resolutionStageRunner: ResolutionStageRunner,
    val topLevelScopes: List<FirScope>,
    val localScopes: List<FirLocalScope>
) {

    val session: FirSession get() = components.session

    private fun processImplicitReceiver(
        towerDataConsumer: TowerDataConsumer,
        implicitReceiverValue: ImplicitReceiverValue<*>,
        nonEmptyLocalScopes: List<FirLocalScope>,
        oldGroup: Int
    ): Int {
        var group = oldGroup
        // Member (no explicit receiver) / extension member (with explicit receiver) access via implicit receiver
        // class Foo(val x: Int) {
        //     fun Bar.baz() {}
        //     fun test() { x }
        //     fun test(b: Bar) { b.baz() }
        // }
        towerDataConsumer.consume(
            TOWER_LEVEL,
            MemberScopeTowerLevel(session, components, dispatchReceiver = implicitReceiverValue, scopeSession = components.scopeSession),
            group++
        )

        // class Foo {
        //     fun foo(block: Foo.() -> Unit) {
        //         block()
        //     }
        // }
        // invokeExtension on local variable
        towerDataConsumer.consume(
            EMPTY,
            TowerScopeLevel.OnlyImplicitReceiver(implicitReceiverValue),
            group++
        )
        //TowerData.OnlyImplicitReceiver(implicitReceiver).process()?.let { return it }

        // Same receiver is dispatch & extension
//        class Foo {
//            fun Foo.bar() {}
//            fun test() { bar() }
//        }
        towerDataConsumer.consume(
            TOWER_LEVEL,
            MemberScopeTowerLevel(
                session, components,
                dispatchReceiver = implicitReceiverValue,
                implicitExtensionReceiver = implicitReceiverValue,
                scopeSession = components.scopeSession
            ),
            group++
        )

        for (scope in nonEmptyLocalScopes) {
            // Local scope extensions via implicit receiver
            // class Foo {
            //     fun test() {
            //         fun Foo.bar() {}
            //         bar()
            //     }
            // }
            towerDataConsumer.consume(
                TOWER_LEVEL,
                ScopeTowerLevel(session, components, scope, implicitExtensionReceiver = implicitReceiverValue),
                group++
            )
        }

        var blockDispatchReceivers = false

        for (implicitDispatchReceiverValue in implicitReceiverValues) {
            val implicitScope = implicitDispatchReceiverValue.implicitScope
            if (implicitScope != null) {
                // Extensions in outer object
                //  object Outer {
                //     fun Nested.foo() {}
                //     class Nested {
                //         fun test() { foo() }
                //     }
                // }
                towerDataConsumer.consume(
                    TOWER_LEVEL,
                    ScopeTowerLevel(session, components, implicitScope, implicitExtensionReceiver = implicitReceiverValue),
                    group++
                )
            }
            if (implicitDispatchReceiverValue is ImplicitDispatchReceiverValue) {
                val implicitCompanionScopes = implicitDispatchReceiverValue.implicitCompanionScopes
                for (implicitCompanionScope in implicitCompanionScopes) {
                    // Extension in companion
                    // class My {
                    //     companion object { fun My.foo() {} }
                    //     fun test() { foo() }
                    // }
                    towerDataConsumer.consume(
                        TOWER_LEVEL,
                        ScopeTowerLevel(session, components, implicitCompanionScope, implicitExtensionReceiver = implicitReceiverValue),
                        group++
                    )
                }
                if (blockDispatchReceivers) {
                    continue
                }
                if ((implicitDispatchReceiverValue.boundSymbol.fir as? FirRegularClass)?.isInner == false) {
                    blockDispatchReceivers = true
                }
            }
            if (implicitDispatchReceiverValue !== implicitReceiverValue) {
                // Two different implicit receivers (dispatch & extension)
                // class A
                // class B {
                //     fun A.foo() {}
                // }
                // fun test(a: A, b: B) {
                //     with(a) { with(b) { foo() } }
                // }
                towerDataConsumer.consume(
                    TOWER_LEVEL,
                    MemberScopeTowerLevel(
                        session, components,
                        scopeSession = components.scopeSession,
                        dispatchReceiver = implicitDispatchReceiverValue,
                        implicitExtensionReceiver = implicitReceiverValue
                    ),
                    group++
                )
            }
        }

        return group
    }

    private fun processTopLevelScope(
        towerDataConsumer: TowerDataConsumer,
        topLevelScope: FirScope,
        oldGroup: Int,
        extensionsOnly: Boolean = false
    ): Int {
        var group = oldGroup
        // Top-level extensions via implicit receiver
        // fun Foo.bar() {}
        // class Foo {
        //     fun test() { bar() }
        // }
        for (implicitReceiverValue in implicitReceiverValues) {
            if (towerDataConsumer.consume(
                    TOWER_LEVEL,
                    ScopeTowerLevel(
                        session, components, topLevelScope,
                        implicitExtensionReceiver = implicitReceiverValue,
                        extensionsOnly = extensionsOnly
                    ),
                    group++
                ) == NONE
            ) {
                return group
            }
        }
        // Member of top-level scope & importing scope
        // val x = 0
        // fun test() { x }
        towerDataConsumer.consume(TOWER_LEVEL, ScopeTowerLevel(session, components, topLevelScope), group++)
        return group
    }

    fun reset() {
        collector.newDataSet()
        sleeping.clear()
    }

    val collector = CandidateCollector(components, resolutionStageRunner)
    private lateinit var towerDataConsumer: TowerDataConsumer
    private lateinit var implicitReceiverValues: List<ImplicitReceiverValue<*>>

    private fun towerDataConsumer(info: CallInfo, collector: CandidateCollector): TowerDataConsumer {
        return when (info.callKind) {
            CallKind.VariableAccess -> {
                createVariableAndObjectConsumer(session, info.name, info, components, collector)
            }
            CallKind.Function -> {
                createFunctionConsumer(session, info.name, info, components, collector, this)
            }
            CallKind.CallableReference -> {
                if (info.stubReceiver == null) {
                    createCallableReferencesConsumer(session, info.name, info, components, collector)
                } else {
                    PrioritizedTowerDataConsumer(
                        collector,
                        createCallableReferencesConsumer(
                            session, info.name, info.replaceExplicitReceiver(info.stubReceiver), components, collector
                        ),
                        createCallableReferencesConsumer(
                            session, info.name, info, components, collector
                        )
                    )
                }
            }
            else -> {
                throw AssertionError("Unsupported call kind in tower resolver: ${info.callKind}")
            }
        }
    }

    private fun createExplicitReceiverForInvoke(candidate: Candidate): FirQualifiedAccessExpressionImpl {
        val symbol = candidate.symbol as FirCallableSymbol<*>
        return FirQualifiedAccessExpressionImpl(null).apply {
            calleeReference = FirNamedReferenceWithCandidate(
                null,
                symbol.callableId.callableName,
                candidate
            )
            dispatchReceiver = candidate.dispatchReceiverExpression()
            typeRef = typeCalculator.tryCalculateReturnType(symbol.firUnsafe())
        }
    }

    // Only case when qualifiedReceiver is a package (no classId) is handled here
    private fun runResolverForFullyQualifiedReceiver(
        implicitReceiverValues: List<ImplicitReceiverValue<*>>,
        info: CallInfo,
        collector: CandidateCollector,
        qualifiedReceiver: FirResolvedQualifier
    ): CandidateCollector {
        val qualifierScope = FirExplicitSimpleImportingScope(
            listOf(
                FirResolvedImportImpl(
                    FirImportImpl(null, FqName.topLevel(info.name), false, null),
                    qualifiedReceiver.packageFqName,
                    qualifiedReceiver.relativeClassFqName
                )
            ), session, components.scopeSession
        )
        val candidateFactory = CandidateFactory(components, info)

        when (info.callKind) {
            CallKind.VariableAccess -> {
                qualifierScope.processPropertiesByName(info.name) {
                    collector.consumeCandidate(0, candidateFactory.createCandidate(it, ExplicitReceiverKind.NO_EXPLICIT_RECEIVER))
                }
                qualifierScope.processClassifiersByName(info.name) {
                    if (it is FirClassSymbol<*> && it.fir.classKind == ClassKind.OBJECT) {
                        collector.consumeCandidate(0, candidateFactory.createCandidate(it, ExplicitReceiverKind.NO_EXPLICIT_RECEIVER))
                    }
                }
            }
            CallKind.Function -> {
                qualifierScope.processFunctionsAndConstructorsByName(info.name, session, components) {
                    collector.consumeCandidate(0, candidateFactory.createCandidate(it, ExplicitReceiverKind.NO_EXPLICIT_RECEIVER))
                }

                val invokeReceiverCollector = CandidateCollector(components, components.resolutionStageRunner)
                val invokeReceiverCandidateFactory = CandidateFactory(
                    components,
                    info.replaceWithVariableAccess()
                )

                qualifierScope.processPropertiesByName(info.name) {
                    invokeReceiverCollector.consumeCandidate(
                        0, invokeReceiverCandidateFactory.createCandidate(it, ExplicitReceiverKind.NO_EXPLICIT_RECEIVER)
                    )
                }
                if (invokeReceiverCollector.isSuccess()) {
                    for (invokeReceiverCandidate in invokeReceiverCollector.bestCandidates()) {
                        val invokeReceiverExpression = createExplicitReceiverForInvoke(invokeReceiverCandidate).let {
                            components.transformQualifiedAccessUsingSmartcastInfo(it)
                        }
                        runResolver(
                            implicitReceiverValues,
                            info.copy(explicitReceiver = invokeReceiverExpression, name = OperatorNameConventions.INVOKE),
                            collector
                        )
                    }
                }
            }
            CallKind.CallableReference -> return collector
            else -> throw AssertionError("Unsupported call kind in tower resolver: ${info.callKind}")
        }
        return collector
    }

    fun runResolver(
        implicitReceiverValues: List<ImplicitReceiverValue<*>>,
        info: CallInfo,
        collector: CandidateCollector = this.collector
    ): CandidateCollector {
        this.implicitReceiverValues = implicitReceiverValues

        val receiver = info.explicitReceiver
        if (receiver is FirResolvedQualifier && receiver.classId == null) {
            return runResolverForFullyQualifiedReceiver(implicitReceiverValues, info, collector, receiver)
        }
        return runResolverForUnqualifiedReceiverEntry(implicitReceiverValues, info, collector)

        towerDataConsumer = towerDataConsumer(info, collector)
        val shouldProcessExtensionsBeforeMembers =
            info.callKind == CallKind.Function && info.name in HIDES_MEMBERS_NAME_LIST
        val shouldProcessExplicitReceiverScopeOnly =
            info.callKind == CallKind.Function && info.explicitReceiver?.typeRef?.coneTypeSafe<ConeIntegerLiteralType>() != null

        var group = 0

        // Specific case when extension should be processed before members (Kotlin forEach vs Java forEach)
        if (shouldProcessExtensionsBeforeMembers) {
            for (topLevelScope in topLevelScopes) {
                group = processTopLevelScope(towerDataConsumer, topLevelScope, group, extensionsOnly = true)
            }
        }

        // Member of explicit receiver' type (this stage does nothing without explicit receiver)
        // class Foo(val x: Int)
        // fun test(f: Foo) { f.x }
        towerDataConsumer.consume(EMPTY, TowerScopeLevel.Empty, group++)

        if (shouldProcessExplicitReceiverScopeOnly) {
            return collector
        }

        // Member of local scope
        // fun test(x: Int) = x
        val nonEmptyLocalScopes = mutableListOf<FirLocalScope>()
        for (scope in localScopes) {
            if (towerDataConsumer.consume(TOWER_LEVEL, ScopeTowerLevel(session, components, scope), group++) != NONE) {
                nonEmptyLocalScopes += scope
            }
        }

        var blockDispatchReceivers = false

        // Member of implicit receiver' type *and* relevant scope
        for (implicitReceiverValue in implicitReceiverValues) {
            if (!blockDispatchReceivers || implicitReceiverValue !is ImplicitDispatchReceiverValue) {
                // Direct use of implicit receiver (see inside)
                group = processImplicitReceiver(towerDataConsumer, implicitReceiverValue, nonEmptyLocalScopes, group)
            }
            val implicitScope = implicitReceiverValue.implicitScope
            if (implicitScope != null) {
                // Regular implicit receiver scope (outer objects, statics)
                // object Outer {
                //     val x = 0
                //     class Nested { val y = x }
                // }
                towerDataConsumer.consume(TOWER_LEVEL, ScopeTowerLevel(session, components, implicitScope), group++)
            }
            if (implicitReceiverValue is ImplicitDispatchReceiverValue) {
                val implicitCompanionScopes = implicitReceiverValue.implicitCompanionScopes
                for (implicitCompanionScope in implicitCompanionScopes) {
                    // Companion scope bound to implicit receiver scope
                    // class Outer {
                    //     companion object { val x = 0 }
                    //     class Nested { val y = x }
                    // }
                    towerDataConsumer.consume(TOWER_LEVEL, ScopeTowerLevel(session, components, implicitCompanionScope), group++)
                }
                if ((implicitReceiverValue.boundSymbol.fir as? FirRegularClass)?.isInner == false) {
                    blockDispatchReceivers = true
                }
            }
        }

        for (topLevelScope in topLevelScopes) {
            group = processTopLevelScope(towerDataConsumer, topLevelScope, group)
        }

        return collector
    }

    private class TowerScopeLevelProcessor(
        val explicitReceiverKind: ExplicitReceiverKind,
        val resultCollector: CandidateCollector,
        val candidateFactory: CandidateFactory,
        val group: Int,
        val noStatics: Boolean
    ) : TowerScopeLevel.TowerScopeLevelProcessor<AbstractFirBasedSymbol<*>> {
        fun replaceReceiver(explicitReceiver: FirExpression, explicitReceiverKind: ExplicitReceiverKind): TowerScopeLevelProcessor {
            return TowerScopeLevelProcessor(
                explicitReceiverKind, resultCollector,
                CandidateFactory(candidateFactory.bodyResolveComponents, candidateFactory.callInfo.replaceExplicitReceiver(explicitReceiver)),
                group, noStatics
            )
        }

        override fun consumeCandidate(
            symbol: AbstractFirBasedSymbol<*>,
            dispatchReceiverValue: ReceiverValue?,
            implicitExtensionReceiverValue: ImplicitReceiverValue<*>?,
            builtInExtensionFunctionReceiverValue: ReceiverValue?
        ) {
            if (noStatics && ((symbol.fir as? FirCallableMemberDeclaration<*>)?.isStatic == true || (symbol.fir as? FirConstructor)?.isInner == false)) return
            // TODO: check extension receiver for default package members (?!)
            // See TowerLevelKindTowerProcessor
            resultCollector.consumeCandidate(
                group, candidateFactory.createCandidate(
                    symbol,
                    explicitReceiverKind,
                    dispatchReceiverValue,
                    implicitExtensionReceiverValue,
                    builtInExtensionFunctionReceiverValue
                )
            )
        }
    }

    data class WaitingForGroup(val continuation: Continuation<Unit>, val groupNum: Int)

    val sleeping = ArrayDeque<WaitingForGroup>()

    suspend fun waitGroup(num: Int) {
        if (collector.isSuccess() && collector.currentGroup <= num) suspendCoroutine<Unit> { }
        val q = sleeping.peekFirst()
        if (q == null || q.groupNum > num) return


        suspendCoroutine<Unit> {
            sleeping.addLast(WaitingForGroup(it, num))
        }
    }

    private inner class LevelHandler(
        val info: CallInfo,
        val receiverValue: AbstractExplicitReceiver<*>?,
        val resultCollector: CandidateCollector,
        val groupMultiplier: Int = 1,
        val groupOffset: Int = 0
    ) {
        var group = 0
        val invokeReceiverCollector = CandidateCollector(components, components.resolutionStageRunner)

        suspend fun nextGroup() {
            group++
            waitGroup(group)
        }

        suspend fun nextGroup(num: Int) {
            group += num
            waitGroup(group)
        }

        private fun TowerScopeLevel.explicitReceiverKind(receiverValue: AbstractExplicitReceiver<*>?): ExplicitReceiverKind {
            return when {
                receiverValue == null -> {
                    ExplicitReceiverKind.NO_EXPLICIT_RECEIVER
                }
                receiverValue is QualifierReceiver -> {
                    if (this is MemberScopeTowerLevel) {
                        ExplicitReceiverKind.NO_EXPLICIT_RECEIVER
                    } else {
                        ExplicitReceiverKind.EXTENSION_RECEIVER
                    }
                }
                this is MemberScopeTowerLevel && dispatchReceiver is AbstractExplicitReceiver<*> -> {
                    ExplicitReceiverKind.DISPATCH_RECEIVER
                }
                else -> {
                    ExplicitReceiverKind.EXTENSION_RECEIVER
                }
            }
        }

        fun TowerScopeLevel.handleLevel(): LevelHandler {
            val candidateFactory = CandidateFactory(components, info)
            val explicitReceiverKind = explicitReceiverKind(receiverValue)
//            val implicitExtensionInvokeMode = (this as? MemberScopeTowerLevel)?.implicitExtensionInvokeMode == true
            val processor =
                TowerScopeLevelProcessor(
                    explicitReceiverKind,
                    resultCollector,
                    candidateFactory,
                    (groupOffset + group) * groupMultiplier * 2,
                    this is MemberScopeTowerLevel && receiverValue !is QualifierReceiver
                )
            val processor2 =
                TowerScopeLevelProcessor(
                    explicitReceiverKind,
                    resultCollector,
                    candidateFactory,
                    (groupOffset + group) * groupMultiplier * 2 + 1,
                    this is MemberScopeTowerLevel && receiverValue !is QualifierReceiver
                )
            when (info.callKind) {
                CallKind.VariableAccess -> {
                    processElementsByName(TowerScopeLevel.Token.Properties, info.name, receiverValue, processor)
                    if (this is MemberScopeTowerLevel || receiverValue == null) {
                        processElementsByName(TowerScopeLevel.Token.Objects, info.name, receiverValue, processor2)
                    }
                }
                CallKind.Function -> {
                    processElementsByName(TowerScopeLevel.Token.Functions, info.name, receiverValue, processor)


                    if (resultCollector.isSuccess()) return this@LevelHandler

                    val prev = invokeReceiverCollector.isSuccess()
                    if (!invokeReceiverCollector.isSuccess()) {
                        val invokeReceiverCandidateFactory = CandidateFactory(
                            components,
                            info.replaceWithVariableAccess()
                        )
                        val invokeReceiverProcessor = TowerScopeLevelProcessor(
                            explicitReceiverKind,
                            invokeReceiverCollector,
                            invokeReceiverCandidateFactory,
                            group,
                            this is MemberScopeTowerLevel && receiverValue !is QualifierReceiver
                        )
                        processElementsByName(TowerScopeLevel.Token.Properties, info.name, receiverValue, invokeReceiverProcessor)
                    }

                    if (!prev && invokeReceiverCollector.isSuccess()) {
                        for (invokeReceiverCandidate in invokeReceiverCollector.bestCandidates()) {
                            val extensionReceiverExpression = invokeReceiverCandidate.extensionReceiverExpression()

                            val symbol = invokeReceiverCandidate.symbol as FirVariableSymbol<*>
                            val useExtensionReceiverAsArgument =
                                symbol.fir.receiverTypeRef == null &&
                                        invokeReceiverCandidate.explicitReceiverKind == ExplicitReceiverKind.EXTENSION_RECEIVER &&
                                        symbol.fir.returnTypeRef.isExtensionFunctionType()
                            val invokeReceiverExpression = createExplicitReceiverForInvoke(invokeReceiverCandidate).let {
                                if (!useExtensionReceiverAsArgument) {
                                    it.extensionReceiver = extensionReceiverExpression
                                }
                                components.transformQualifiedAccessUsingSmartcastInfo(it)
                            }

                            val invokeFunctionInfo =
                                info.copy(explicitReceiver = invokeReceiverExpression, name = OperatorNameConventions.INVOKE).let {
                                    if (useExtensionReceiverAsArgument) it.withReceiverAsArgument(extensionReceiverExpression)
                                    else it
                                }

                            val explicitReceiver = invokeFunctionInfo.explicitReceiver?.let { qualifierOrExpressionReceiver(it) }
                            val handler = LevelHandler(invokeFunctionInfo, explicitReceiver, resultCollector, 2, 0)


                            val coroutine = suspend {
                                runResolverForUnqualifiedReceiver(
                                    explicitReceiver,
                                    implicitReceiverValues,
                                    invokeFunctionInfo,
                                    resultCollector,
                                    handler
                                )
                                Unit
                            }.createCoroutine(object : Continuation<Unit> {
                                override val context: CoroutineContext
                                    get() = EmptyCoroutineContext

                                override fun resumeWith(result: Result<Unit>) {}
                            })
                            sleeping.add(WaitingForGroup(coroutine, 0))

                        }
                    }
                }
                CallKind.CallableReference -> {
                    val stubReceiver = info.stubReceiver
                    if (stubReceiver != null) {
                        val stubReceiverValue = qualifierOrExpressionReceiver(stubReceiver)
                        val stubProcessor = processor.replaceReceiver(stubReceiver, explicitReceiverKind(stubReceiverValue))
                        processElementsByName(TowerScopeLevel.Token.Functions, info.name, stubReceiverValue, stubProcessor)
                        processElementsByName(TowerScopeLevel.Token.Properties, info.name, stubReceiverValue, stubProcessor)
                        processElementsByName(TowerScopeLevel.Token.Functions, info.name, receiverValue, processor2)
                        processElementsByName(TowerScopeLevel.Token.Properties, info.name, receiverValue, processor2)
                    } else {
                        processElementsByName(TowerScopeLevel.Token.Functions, info.name, receiverValue, processor)
                        processElementsByName(TowerScopeLevel.Token.Properties, info.name, receiverValue, processor)
                    }
                }
                else -> {
                    throw AssertionError("Unsupported call kind in tower resolver: ${info.callKind}")
                }
            }
            return this@LevelHandler
        }
    }

    private fun runResolverForUnqualifiedReceiverEntry(
        implicitReceiverValues: List<ImplicitReceiverValue<*>>,
        info: CallInfo,
        collector: CandidateCollector
    ): CandidateCollector {
        val explicitReceiverValue = info.explicitReceiver?.let { qualifierOrExpressionReceiver(it) }
        val levelHandler = LevelHandler(info, explicitReceiverValue, collector)
        val coroutine = suspend {
            runResolverForUnqualifiedReceiver(explicitReceiverValue, implicitReceiverValues, info, collector, levelHandler)
            Unit
        }.createCoroutine(object : Continuation<Unit> {
            override val context: CoroutineContext
                get() = EmptyCoroutineContext

            override fun resumeWith(result: Result<Unit>) {}
        })
        sleeping.add(WaitingForGroup(coroutine, 0))
        while (sleeping.isNotEmpty()) {
            val first = sleeping.pollFirst()!!
            first.continuation.resume(Unit)
        }
        return collector
    }

    private suspend fun runResolverForUnqualifiedReceiver(
        explicitReceiverValue: AbstractExplicitReceiver<*>?,
        implicitReceiverValues: List<ImplicitReceiverValue<*>>,
        info: CallInfo,
        collector: CandidateCollector,
        levelHandler: LevelHandler
    ) {

        with(levelHandler) {
            val shouldProcessExtensionsBeforeMembers =
                info.callKind == CallKind.Function && info.name in HIDES_MEMBERS_NAME_LIST
            if (shouldProcessExtensionsBeforeMembers) {
                // Special case (extension hides member)
                for (topLevelScope in topLevelScopes) {
                    ScopeTowerLevel(
                        session, components, topLevelScope, extensionsOnly = true
                    ).handleLevel().nextGroup()
                }
            }

            // 1. Non-extension members
            if (explicitReceiverValue == null) nextGroup()
            else {
                MemberScopeTowerLevel(
                    session, components, dispatchReceiver = explicitReceiverValue, scopeSession = components.scopeSession
                ).handleLevel().nextGroup()
            }

            val shouldProcessExplicitReceiverScopeOnly =
                info.callKind == CallKind.Function && info.explicitReceiver?.typeRef?.coneTypeSafe<ConeIntegerLiteralType>() != null
            if (shouldProcessExplicitReceiverScopeOnly) {
                // Special case (integer literal type)
                return
            }

            for (localScope in localScopes) {
                ScopeTowerLevel(
                    session, components, localScope
                ).handleLevel().nextGroup()
            }

            for (implicitReceiverValue in implicitReceiverValues) {
                // TODO: move to 1?
                MemberScopeTowerLevel(
                    session, components, dispatchReceiver = implicitReceiverValue, scopeSession = components.scopeSession
                ).handleLevel().nextGroup()

                if (explicitReceiverValue == null) nextGroup()
                else MemberScopeTowerLevel(
                    session, components, dispatchReceiver = explicitReceiverValue,
                    implicitExtensionReceiver = implicitReceiverValue,
                    implicitExtensionInvokeMode = true,
                    scopeSession = components.scopeSession
                ).handleLevel().nextGroup()

//                MemberScopeTowerLevel(
//                    session, components, dispatchReceiver = implicitReceiverValue, implicitExtensionReceiver = implicitReceiverValue, scopeSession = components.scopeSession
//                ).handleLevel().nextGroup()

                //
                for (scope in localScopes) {
                    ScopeTowerLevel(
                        session, components, scope, implicitExtensionReceiver = implicitReceiverValue
                    ).handleLevel().nextGroup()
                }

                if (explicitReceiverValue == null) {
                    // NB: no-receiver specific
                    for (implicitExtensionReceiverValue in implicitReceiverValues) {
                        MemberScopeTowerLevel(
                            session,
                            components,
                            dispatchReceiver = implicitReceiverValue,
                            implicitExtensionReceiver = implicitExtensionReceiverValue,
                            scopeSession = components.scopeSession
                        ).handleLevel().nextGroup()
                    }
                } else {
                    nextGroup(implicitReceiverValues.size)
                }

                if (implicitReceiverValue is ImplicitDispatchReceiverValue) {
                    val implicitCompanionScopes = implicitReceiverValue.implicitCompanionScopes
                    if (explicitReceiverValue == null) {
                        val implicitReceiverScope = implicitReceiverValue.scope(session, components.scopeSession)
                        if (implicitReceiverScope != null) {
                            ScopeTowerLevel(
                                session,
                                components,
                                FirStaticScope(implicitReceiverScope)
                            ).handleLevel().nextGroup()
                        }
                        for (implicitCompanionScope in implicitCompanionScopes) {
                            // Companion scope bound to implicit receiver scope
                            // class Outer {
                            //     companion object { val x = 0 }
                            //     class Nested { val y = x }
                            // }
                            ScopeTowerLevel(session, components, implicitCompanionScope).handleLevel().nextGroup()


                            ScopeTowerLevel(
                                session,
                                components,
                                implicitCompanionScope,
                                implicitExtensionReceiver = implicitReceiverValue
                            ).handleLevel().nextGroup()
                        }
                    } else {
                        nextGroup(implicitCompanionScopes.size)
                    }
                }

            }

            // 3-6. Top-level & importing scopes
            for (topLevelScope in topLevelScopes) {

                if (explicitReceiverValue != null) nextGroup(implicitReceiverValues.size)
                else {
                    for (implicitReceiverValue in implicitReceiverValues) {
                        ScopeTowerLevel(
                            session, components, topLevelScope, implicitExtensionReceiver = implicitReceiverValue
                        ).handleLevel().nextGroup()
                    }
                }

                ScopeTowerLevel(
                    session, components, topLevelScope
                ).handleLevel().nextGroup()
            }

        }
    }


}
