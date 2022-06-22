// RUN: %dafny /compile:0 /useRuntimeLib /spillTargetCode:3 /out:%S/Input/producer %S/Input/producer/timesTwo.dfy
// RUN: dotnet build %S/Input/producer

// RUN: %dafny /compile:0 /useRuntimeLib /out:%S/consumer /library %S/Input/producer/timesTwo.dfy /spillTargetCode:3 %s
// RUN: dotnet run --project %S/consumer > "%t"
// RUN: %diff "%s.expect" "%t"

include "Input/producer/timesTwo.dfy"

module ConsumerModule {

  import opened LibraryModule

  method Main() {
    var n := 21;
    var TwoN := TimesTwo(n);
    print "Two times ", n, " is ", TwoN, "\n";
  }
}