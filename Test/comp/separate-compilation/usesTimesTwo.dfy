// RUN: %translate cs %trargs --output=%S/Inputs/producer/timesTwo %S/Inputs/producer/timesTwo.dfy
// RUN: dotnet build %S/Inputs/producer

// RUN: %translate cs --output=%S/consumer/usesTimesTwo --library=%S/Inputs/producer/timesTwo.dfy %s
// RUN: dotnet run --project %S/consumer > "%t"
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
