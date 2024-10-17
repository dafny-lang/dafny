// NONUNIFORM: Highly target language specific

// Alternate version of usesTimesTwo.dfy as a regression test for https://github.com/dafny-lang/dafny/issues/5555.
// Relies on having checked in the compilation of the library using Dafny 4.2.

// Java

// RUN: %baredafny translate java --output=%S/Inputs/producer/timesTwo %S/Inputs/producer/timesTwo.dfy --legacy-data-constructors --legacy-module-names
// RUN: javac -cp %binaryDir/DafnyRuntime.jar%{pathsep}%S/Inputs/producer/timesTwo-java %S/Inputs/producer/timesTwo-java/**/*.java

// Already run using Dafny 4.2: %baredafny translate java --output=%S/fromDafny42/usesTimesTwo --allow-warnings --library=%S/Inputs/producer/timesTwo.dfy %S/usesTimesTwo.dfy
// RUN: javac -cp %binaryDir/DafnyRuntime.jar%{pathsep}%S/Inputs/producer/timesTwo-java%{pathsep}%S/fromDafny42/usesTimesTwo-java %S/fromDafny42/usesTimesTwo-java/**/*.java

// RUN: java -cp %binaryDir/DafnyRuntime.jar%{pathsep}%S/Inputs/producer/timesTwo-java%{pathsep}%S/fromDafny42/usesTimesTwo-java usesTimesTwo > "%t"

// (Other languages could be added in the future too.)

// Final output check for all runs

// RUN: %diff "%s.expect" "%t"