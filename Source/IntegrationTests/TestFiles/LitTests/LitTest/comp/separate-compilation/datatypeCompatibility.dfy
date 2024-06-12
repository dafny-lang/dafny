// RUN: %baredafny build %args -t:java %s
// RUN: javac Test.java -cp %S/datatypeCompatibility.jar

module Wrappers {
  datatype Option<+T> = Some(value: T) | None
}