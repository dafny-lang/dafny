// NONUNIFORM: this fails on Java
// RUN: %run --target go %s > %t
// RUN: %diff "%s.expect" "%t"

module DuplicateName {
  const x := 3 
}

module ProblemModule {
  datatype DuplicateName = DuplicateName
}

import D = DuplicateName

method Main() {
  print D.x;
}

