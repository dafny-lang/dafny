// RUN: %dafny /compile:1 /spillTargetCode:2 /compileTarget:java "%s" > "%t"
// RUN: javac -cp %binaryDir/DafnyRuntime.jar:%S/git-issue-2071-java %S/git-issue-2071-java/git_issue_2071.java %S/git-issue-2071-java/*/*.java
// RUN: java -ea -cp %binaryDir/DafnyRuntime.jar:%S/git-issue-2071-java git_issue_2071 >> "%t"
// RUN: %diff "%s.expect" "%t"

function method singletonSeq<T>(x: T): seq<T> {
  [x]
}

datatype MyDatatype = MyDatatype

method Main() {
  // OK
  print [MyDatatype], "\n";

  // Assertion failure
  print singletonSeq(MyDatatype), "\n";
}