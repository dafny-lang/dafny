// NONUNIFORM: Highly target language specific

// Java

// Already run using Dafny 4.2: %baredafny translate java --output=%S/Inputs/producer/fromDafny42/timesTwo %S/Inputs/producer/timesTwo.dfy

// RUN: javac -cp %binaryDir/DafnyRuntime.jar%{pathsep}%S/Inputs/producer/fromDafny42/timesTwo-java %S/Inputs/producer/fromDafny42/timesTwo-java/timesTwo.java

// RUN: %baredafny translate java --output=%S/consumer/usesTimesTwo --allow-warnings --library=%S/Inputs/producer/timesTwo.dfy %S/usesTimesTwo.dfy
// RUN: javac -cp %binaryDir/DafnyRuntime.jar%{pathsep}%S/Inputs/producer/fromDafny42/timesTwo-java%{pathsep}%S/consumer/usesTimesTwo-java %S/consumer/usesTimesTwo-java/usesTimesTwo.java

// RUN: java -cp %binaryDir/DafnyRuntime.jar%{pathsep}%S/Inputs/producer/fromDafny42/timesTwo-java%{pathsep}%S/consumer/usesTimesTwo-java usesTimesTwo >> "%t"
