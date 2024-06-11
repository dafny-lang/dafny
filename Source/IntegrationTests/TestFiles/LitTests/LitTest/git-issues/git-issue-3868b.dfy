// RUN: %baredafny translate java %args %s --output=%S/git-issue-3868b
// RUN: %OutputCheck --file-to-check %S/git-issue-3868b-java/_System/__default.java "%s"
// CHECK-NOT: Let\(

// If the nested let expressions in the following function generate nested lambdas in Java,
// then the Java compiler chokes (either by taking a very long time or by giving some error).
// As an extra precautionary measure that we don't generate nested lambdas, the test files
//     git-issue-3868a.dfy
//     git-issue-3868b.dfy
// use OutputCheck to look for occurrences of "Let(" in the target .java file. In this file,
// we expect there not to be any occurrences of "Let(". But this test could fail for the wrong
// reason (for example, if the Java "Let" function is renamed in the future), so we also
// check in git-issue-3868a.dfy that there _is_ an occurrence of "Let(".

datatype Or = A | B

function WoahThat'sDeep(o: Or, x: string): Option<string> {
  var r :- match o {
    case A =>
      var x1 := x;
      var x2 := x1;
      var x3 := x2;
      var x4 := x3;
      var x5 := x4;
      var x6 := x5;
      var x7 := x6;
      var x8 := x7;
      var x9 := x8;
      var x10 := x9;
      Some(x10)
    case B =>
      Some("hello")
  };
  Some(r)
}

datatype Option<+T> = None | Some(value: T) {
  predicate IsFailure() {
    None?
  }

  function PropagateFailure<U>(): Option<U>
    requires None?
  {
    None
  }

  function Extract(): T
    requires Some?
  {
    value
  }
}
