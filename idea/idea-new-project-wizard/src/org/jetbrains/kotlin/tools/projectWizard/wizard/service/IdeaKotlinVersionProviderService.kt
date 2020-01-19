/*
 * Copyright 2010-2020 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.tools.projectWizard.wizard.service

import org.jetbrains.kotlin.idea.KotlinPluginUtil
import org.jetbrains.kotlin.tools.projectWizard.core.service.WizardKotlinVersion
import org.jetbrains.kotlin.tools.projectWizard.core.service.KotlinVersionKind
import org.jetbrains.kotlin.tools.projectWizard.core.service.KotlinVersionProviderService
import org.jetbrains.kotlin.tools.projectWizard.settings.version.Version

class IdeaKotlinVersionProviderService : KotlinVersionProviderService, IdeaWizardService {
    override fun getKotlinVersion(): WizardKotlinVersion {
//        if (KotlinPluginUtil.isSnapshotVersion()) return WizardKotlinVersion.DEFAULT
        val version = Version.fromString("1.3.70-eap-42")
        return WizardKotlinVersion(version, version.kotlinVersionKind())
    }

    private fun Version.kotlinVersionKind() = when {
        "eap" in toString() -> KotlinVersionKind.EAP
        "dev" in toString() -> KotlinVersionKind.DEV
        else -> KotlinVersionKind.STABLE
    }
}