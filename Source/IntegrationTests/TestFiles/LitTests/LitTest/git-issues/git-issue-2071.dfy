// RUN: %translate java %trargs "%s" > "%t"
// RUN: javac -cp %binaryDir/DafnyRuntime.jar%{pathsep}%S/git-issue-2071-java %S/git-issue-2071-java/git_issue_2071.java %S/git-issue-2071-java/*/*.java >> "%t"
// RUN: java -ea -cp %binaryDir/DafnyRuntime.jar%{pathsep}%S/git-issue-2071-java git_issue_2071 >> "%t"
// RUN: %diff "%s.expect" "%t"

function singletonSeq<T>(x: T): seq<T> {
  [x]
}

datatype MyDatatype = MyDatatype

method Main() {
  // OK
  print [MyDatatype], "\n";

  // Assertion failure
  print singletonSeq(MyDatatype), "\n";
}
