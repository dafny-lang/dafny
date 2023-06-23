/*
 * Copyright 2014-2021 the original author or authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
plugins {
    `java-library`
    id("me.champeau.jmh") version "0.7.0"
}

repositories {
    mavenLocal()
    mavenCentral()
}

dependencies {
    implementation("org.dafny:DafnyRuntime:4.1.0")
    testImplementation("org.junit.jupiter:junit-jupiter-api:5.9.2")
    testRuntimeOnly("org.junit.jupiter:junit-jupiter-engine")
}

tasks.test {
    useJUnitPlatform()
}

jmh {
    warmupIterations.set(2)
    iterations.set(20)
    timeOnIteration.set("1s")
    fork.set(2)
    threads.set(10)
}

/*

To actually generate and run the benchmark:

dafny translate java src/benchmark/dafny/SequenceRace.dfy --plugin:../../../Binaries/net6.0/DafnyBenchmarkingPlugin.dll
mv src/benchmark/dafny/SequenceRace-java src/jmh/java
gradle jmh

This exposes https://github.com/dafny-lang/dafny/issues/1454 100% of the time based on a few local runs.
 */