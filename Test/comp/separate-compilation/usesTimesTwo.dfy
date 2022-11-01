// C#

// RUN: %baredafny translate --output=%S/Inputs/producer/timesTwo %S/Inputs/producer/timesTwo.dfy
// RUN: dotnet build %S/Inputs/producer

// RUN: %baredafny translate --output=%S/consumer/usesTimesTwo --library=%S/Inputs/producer/timesTwo.dfy %s
// RUN: dotnet run --project %S/consumer > "%t"

// Java

// RUN: %baredafny translate --target=java --output=%S/Inputs/producer/timesTwo %S/Inputs/producer/timesTwo.dfy
// RUN: javac -cp %binaryDir/DafnyRuntime.jar:%S/Inputs/producer/timesTwo-java %S/Inputs/producer/timesTwo-java/timesTwo.java %S/Inputs/producer/timesTwo-java/*/*.java

// RUN: %baredafny translate --target=java --output=%S/consumer/usesTimesTwo --library=%S/Inputs/producer/timesTwo.dfy %s
// RUN: javac -cp %binaryDir/DafnyRuntime.jar:%S/Inputs/producer/timesTwo-java:%S/consumer/usesTimesTwo-java %S/consumer/usesTimesTwo-java/usesTimesTwo.java %S/consumer/usesTimesTwo-java/*/*.java
// RUN: java -cp %binaryDir/DafnyRuntime.jar:%S/Inputs/producer/timesTwo-java:%S/consumer/usesTimesTwo-java usesTimesTwo >> "%t"
// RUN: %diff "%s.expect" "%t"

include "Inputs/producer/timesTwo.dfy"

module ConsumerModule {

  import opened LibraryModule

  method Main() {
    var n := 21;
    var TwoN := TimesTwo(n);
    print "Two times ", n, " is ", TwoN, "\n";
  }
}
