plugins {
    id("application")
    id("tai-e.conventions")
}


dependencies {
    // Process options
    implementation("info.picocli:picocli:4.6.1")
    // Logger
    implementation("org.apache.logging.log4j:log4j-api:2.16.0")
    implementation("org.apache.logging.log4j:log4j-core:2.16.0")
    // Process YAML configuration files
    implementation("com.fasterxml.jackson.dataformat:jackson-dataformat-yaml:2.12.2")
    // Use Soot as frontend
    implementation(files("lib/sootclasses-modified.jar"))
    implementation("org.soot-oss:soot:4.3.0-20211223.212205-256")
    // Eliminate SLF4J warning
    implementation("org.slf4j:slf4j-nop:1.7.5")
    // Neo4j
    implementation("org.neo4j.driver:neo4j-java-driver:5.3.0")

    testImplementation("junit:junit:4.13")
}

application {
    mainClass.set("pascal.taie.Main")
}

task("fatJar", type = Jar::class) {
    group = "build"
    description = "Creates a single jar file including Tai-e and all dependencies"
    manifest {
        attributes["Main-Class"] = "pascal.taie.Main"
    }
    archiveBaseName.set("tai-e-all")
    from(
        configurations.compileClasspath.get().map {
            if (it.isDirectory) it else zipTree(it)
        }
    )
    from("COPYING", "COPYING.LESSER")
    doLast {
        copy {
            from(archiveFile)
            into(rootProject.buildDir)
        }
    }
    duplicatesStrategy = DuplicatesStrategy.EXCLUDE
    with(tasks["jar"] as CopySpec)
}

tasks.test {
    // Increases the maximum heap memory of JUnit test process. The default is 512M.
    // (see org.gradle.process.internal.worker.DefaultWorkerProcessBuilder.build)
    maxHeapSize = "2G"
}

// Automatically agree the Gradle ToS when running gradle with '--scan' option
extensions.findByName("buildScan")?.withGroovyBuilder {
    setProperty("termsOfServiceUrl", "https://gradle.com/terms-of-service")
    setProperty("termsOfServiceAgree", "yes")
}
