// NONUNIFORM: Multiple test scenarios - ideally would still test for each backend though

// RUN: %baredafny build %args -t:lib %S/Inputs/wrappers.dfy > %t
// RUN: %baredafny build %args -t:lib %S/Inputs/seq.dfy --library %S/Inputs/wrappers.doo >> %t
// RUN: %baredafny run   %args %s --library %S/Inputs/seq.doo --library %S/Inputs/wrappers.doo >> %t

// Supported: matching options

// RUN: %baredafny build %args -t:lib --boogie /vcsSplitOnEveryAssert %S/Inputs/wrappers.dfy
// RUN: %baredafny build %args -t:lib --boogie /vcsSplitOnEveryAssert %S/Inputs/seq.dfy --library %S/Inputs/wrappers.doo >> %t

// RUN: %baredafny build %args -t:lib --no-verify %S/Inputs/wrappers.dfy
// RUN: %baredafny build %args -t:lib --no-verify %S/Inputs/seq.dfy --library %S/Inputs/wrappers.doo >> %t

// Supported: mismatching irrelevant options

// RUN: %baredafny build %args -t:lib --function-syntax:3 %S/Inputs/wrappers3.dfy
// RUN: %baredafny build %args -t:lib %S/Inputs/seq.dfy --library %S/Inputs/wrappers3.doo >> %t

// Error cases: mismatched options

// RUN: %baredafny build %args -t:lib --unicode-char true %S/Inputs/wrappers.dfy
// RUN: ! %baredafny build %args -t:lib --allow-deprecation --unicode-char false %S/Inputs/seq.dfy --library %S/Inputs/wrappers.doo >> %t

// RUN: %baredafny build %args -t:lib --boogie /vcsLoad:2 %S/Inputs/wrappers.dfy
// RUN: ! %baredafny build %args -t:lib %S/Inputs/seq.dfy --library %S/Inputs/wrappers.doo >> %t

// RUN: %baredafny build %args -t:lib --no-verify %S/Inputs/wrappers.dfy
// RUN: ! %baredafny build %args -t:lib %S/Inputs/seq.dfy --library %S/Inputs/wrappers.doo >> %t

// RUN: %diff "%s.expect" %t

module App {

  import opened Seq

  method Main() {
    var a := [1, 2, 3];
    var b := [4, 5, 6];
    var c := [7, 8, 9];

    LemmaConcatIsAssociative(a, b, c);
    assert (a + b) + c == a + (b + c);

    print a + b + c, "\n";
  }

}