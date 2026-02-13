// NONUNIFORM: Highly target language specific

// C#

// RUN: %baredafny translate cs %args --output=%S/Inputs/producer/timesTwo %S/Inputs/producer/timesTwo.dfy --outer-module TestProducer.DafnyInternal
// RUN: dotnet build %S/Inputs/producer

// RUN: %baredafny translate cs %args --output=%S/consumer/usesTimesTwo --allow-warnings --library=%S/Inputs/producer/timesTwo.dfy %s --translation-record %S/Inputs/producer/timesTwo-cs.dtr

// RUN: dotnet run --project %S/consumer > "%t"

// Java

// RUN: %baredafny translate java --output=%S/Inputs/producer/timesTwo %S/Inputs/producer/timesTwo.dfy --outer-module testproducer.dafnyinternal --translation-record-output %S/timesTwo-customName.dtr
// RUN: javac -cp %binaryDir/DafnyRuntime.jar%{pathsep}%S/Inputs/producer/timesTwo-java %S/Inputs/producer/timesTwo-java/**/*.java

// RUN: %baredafny translate java --output=%S/consumer/usesTimesTwo --allow-warnings --library=%S/Inputs/producer/timesTwo.dfy %s --translation-record %S/timesTwo-customName.dtr
// RUN: javac -cp %binaryDir/DafnyRuntime.jar%{pathsep}%S/Inputs/producer/timesTwo-java%{pathsep}%S/consumer/usesTimesTwo-java %S/consumer/usesTimesTwo-java/**/*.java

// RUN: java -cp %binaryDir/DafnyRuntime.jar%{pathsep}%S/Inputs/producer/timesTwo-java%{pathsep}%S/consumer/usesTimesTwo-java usesTimesTwo >> "%t"

// Python

// TODO: Can we refer to the runtime separately?
// RUN: %baredafny translate py --output=%S/Inputs/producer/timesTwo %S/Inputs/producer/timesTwo.dfy --include-runtime

// RUN: %baredafny translate py --output=%S/consumer/usesTimesTwo --allow-warnings --library=%S/Inputs/producer/timesTwo.dfy %s

// TODO: Won't work on windows
// RUN: env PYTHONPATH=%S/Inputs/producer/timesTwo-py python3 %S/consumer/usesTimesTwo-py >> "%t"

// Go

// Must --include-runtime since DafnyRuntime.go isn't usable:
// https://github.com/dafny-lang/dafny/issues/494
// RUN: %baredafny translate go --output=%S/Inputs/producer/timesTwo %S/Inputs/producer/timesTwo.dfy --include-runtime

// RUN: %baredafny translate go --output=%S/consumer/usesTimesTwo --allow-warnings --library=%S/Inputs/producer/timesTwo.dfy %s

// RUN: env GO111MODULE=auto GOPATH=%S/Inputs/producer/timesTwo-go%{pathsep}%S/consumer/usesTimesTwo-go go run %S/consumer/usesTimesTwo-go/src/usesTimesTwo.go >> "%t"

// (Javascript doesn't support this yet)

// Final output check for all runs

// RUN: %diff "%s.expect" "%t"

include "Inputs/producer/timesTwo.dfy"

module ConsumerModule {

  import opened CoolLibraryName.LibraryModule
  import Math

  method Main() {
    var n := 21;
    var TwoN := TimesTwo(n);
    print "Two times ", n, " is ", TwoN, "\n";

    var z := Math.Add(20, 22);
    print "20 plus 22 is ", z, "\n";

    // Need to actually execute the use of nat's type descriptor
    // to ensure it works on dynamic language targets.
    var aNat := PickANat();
  }

  method PickANat() returns (n: nat) {
    n := PickSomething<nat>();
  }

  method PickSomething<T(0)>() returns (t: T) {
    t := *;
  }

  method MakeAResult() {
    var r: Result<nat, string> := Success(42);
  }

  method MakeAPair() {
    var p: Pair<nat, string> := Pair(1, "partridge in a pair tree");
  }
}
