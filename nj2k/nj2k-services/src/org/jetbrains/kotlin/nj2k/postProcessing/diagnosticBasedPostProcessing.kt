/*
 * Copyright 2010-2019 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.nj2k.postProcessing

import com.intellij.codeInsight.intention.IntentionAction
import com.intellij.openapi.editor.RangeMarker
import com.intellij.psi.PsiElement
import org.jetbrains.kotlin.caches.resolve.KotlinCacheService
import org.jetbrains.kotlin.diagnostics.Diagnostic
import org.jetbrains.kotlin.diagnostics.DiagnosticFactory
import org.jetbrains.kotlin.idea.caches.resolve.getResolutionFacade
import org.jetbrains.kotlin.idea.core.util.range
import org.jetbrains.kotlin.idea.quickfix.AddExclExclCallFix
import org.jetbrains.kotlin.idea.quickfix.KotlinIntentionActionsFactory
import org.jetbrains.kotlin.idea.quickfix.KotlinSingleIntentionActionFactory
import org.jetbrains.kotlin.idea.resolve.ResolutionFacade
import org.jetbrains.kotlin.idea.util.application.runReadAction
import org.jetbrains.kotlin.nj2k.NewJ2kConverterContext
import org.jetbrains.kotlin.psi.KtElement
import org.jetbrains.kotlin.psi.KtFile
import org.jetbrains.kotlin.psi.psiUtil.elementsInRange
import org.jetbrains.kotlin.resolve.diagnostics.Diagnostics
import org.jetbrains.kotlin.utils.addToStdlib.safeAs

class DiagnosticBasedPostProcessingGroup(diagnosticBasedProcessings: List<DiagnosticBasedProcessing>) : FileBasedPostProcessing() {
    constructor(vararg diagnosticBasedProcessings: DiagnosticBasedProcessing) : this(diagnosticBasedProcessings.toList())

    private val diagnosticToFix =
        diagnosticBasedProcessings.asSequence().flatMap { processing ->
            processing.diagnosticFactories.asSequence().map { it to processing::fix }
        }.groupBy { it.first }.mapValues { (_, list) ->
            list.map { it.second }
        }

    override fun runProcessing(file: KtFile, allFiles: List<KtFile>, rangeMarker: RangeMarker?, converterContext: NewJ2kConverterContext) {
        val resolutionFacade = runReadAction { KotlinCacheService.getInstance(converterContext.project).getResolutionFacade(allFiles) }
        val diagnostics = runReadAction { analyzeFileRange(file, rangeMarker, resolutionFacade).all() }
        runUndoTransparentActionInEdt(inWriteAction = true) {
            for (diagnostic in diagnostics) {
                val range = rangeMarker?.range ?: file.textRange
                if (diagnostic.psiElement.isInRange(range)) {
                    diagnosticToFix[diagnostic.factory]?.forEach { fix ->
                        if (diagnostic.psiElement.isValid) {
                            fix(diagnostic)
                        }
                    }
                }
            }
        }
    }

    private fun analyzeFileRange(file: KtFile, rangeMarker: RangeMarker?, resolutionFacade: ResolutionFacade): Diagnostics {
        val elements = when {
            rangeMarker == null -> listOf(file)
            rangeMarker.isValid -> file.elementsInRange(rangeMarker.range!!).filterIsInstance<KtElement>()
            else -> emptyList()
        }

        return if (elements.isNotEmpty())
            resolutionFacade.analyzeWithAllCompilerChecks(elements).bindingContext.diagnostics
        else Diagnostics.EMPTY
    }
}

interface DiagnosticBasedProcessing {
    val diagnosticFactories: List<DiagnosticFactory<*>>
    fun fix(diagnostic: Diagnostic)
}

inline fun <reified T : PsiElement> diagnosticBasedProcessing(
    vararg diagnosticFactory: DiagnosticFactory<*>,
    crossinline fix: (T, Diagnostic) -> Unit
) =
    object : DiagnosticBasedProcessing {
        override val diagnosticFactories = diagnosticFactory.toList()
        override fun fix(diagnostic: Diagnostic) {
            val element = diagnostic.psiElement as? T
            if (element != null) {
                fix(element, diagnostic)
            }
        }
    }

fun diagnosticBasedProcessing(fixFactory: KotlinIntentionActionsFactory, vararg diagnosticFactory: DiagnosticFactory<*>) =
    object : DiagnosticBasedProcessing {
        override val diagnosticFactories = diagnosticFactory.toList()
        override fun fix(diagnostic: Diagnostic) {
            val fix = fixFactory.createActions(diagnostic).singleOrNull()
            fix?.invoke(diagnostic.psiElement.project, null, diagnostic.psiFile)
        }
    }

fun addExclExclFactoryNoImplicitReceiver(initialFactory: KotlinSingleIntentionActionFactory) =
    object : KotlinSingleIntentionActionFactory() {
        override fun createAction(diagnostic: Diagnostic): IntentionAction? =
            initialFactory.createActions(diagnostic).singleOrNull()
                ?.safeAs<AddExclExclCallFix>()
                ?.let {
                    AddExclExclCallFix(diagnostic.psiElement, checkImplicitReceivers = false)
                }
    }

