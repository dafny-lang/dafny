// NONUNIFORM: Highly target language specific

// Java

// RUN: %baredafny translate java --output=%S/Inputs/producer/timesTwo %S/Inputs/producer/timesTwo.dfy
// RUN: javac -cp %binaryDir/DafnyRuntime.jar%{pathsep}%S/Inputs/producer/timesTwo-java %S/Inputs/producer/timesTwo-java/timesTwo.java

// Already run using Dafny 4.2: %baredafny translate java --output=%S/fromDafny42/usesTimesTwo --allow-warnings --library=%S/Inputs/producer/timesTwo.dfy %S/usesTimesTwo.dfy
// RUN: javac -cp %binaryDir/DafnyRuntime.jar%{pathsep}%S/Inputs/producer/timesTwo-java%{pathsep}%S/fromDafny42/usesTimesTwo-java %S/fromDafny42/usesTimesTwo-java/usesTimesTwo.java

// RUN: java -cp %binaryDir/DafnyRuntime.jar%{pathsep}%S/Inputs/producer/timesTwo-java%{pathsep}%S/fromDafny42/usesTimesTwo-java usesTimesTwo >> "%t"
