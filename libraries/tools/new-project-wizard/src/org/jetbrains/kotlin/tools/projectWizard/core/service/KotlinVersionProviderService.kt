/*
 * Copyright 2010-2020 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.tools.projectWizard.core.service

import org.jetbrains.kotlin.tools.projectWizard.settings.version.Version

interface KotlinVersionProviderService : WizardService {
    fun getKotlinVersion(): WizardKotlinVersion
}

class KotlinVersionProviderServiceImpl : KotlinVersionProviderService, IdeaIndependentWizardService {
    // For now used only for tests
    override fun getKotlinVersion(): WizardKotlinVersion =
        WizardKotlinVersion(
            Version.fromString("1.3.61"),
            KotlinVersionKind.STABLE
        )
}

data class WizardKotlinVersion(
    val version: Version,
    val kind: KotlinVersionKind
) {
    companion object {
        val DEFAULT = WizardKotlinVersion(Version.fromString("1.3.61"), KotlinVersionKind.STABLE)
    }
}

fun WizardKotlinVersion.getPreviousStable(): WizardKotlinVersion? {
    if (kind == KotlinVersionKind.STABLE) return null
    val incremental = version.incremental
    if (incremental > 0) {
        val newIncrementalVersion = when {
            incremental % 10 == 0 -> incremental - 10
            else -> incremental - 1
        }
        return WizardKotlinVersion(
            Version.fromComponents(version.major, version.minor, newIncrementalVersion),
            KotlinVersionKind.STABLE
        )
    }
    return null
}


enum class KotlinVersionKind {
    STABLE, EAP, DEV
}