// RUN: %run --target go %s > %t
// RUN: %diff "%s.expect" "%t"

module Producer {
  const x := 3 
}
module DuplicateName {
  // Adding an actual import so we can test that we're not breaking that
  import Producer

  // ProblemModule must come after DuplicateName in the topologic sort, so DuplicateName is compiled before ProblemModule
  // This way, an import to DuplicateName ends up in ProblemModule, which triggers the bug
  import ProblemModule
  const y := Producer.x 
}

module ProblemModule {
  datatype DuplicateName = DuplicateName
}

import D = DuplicateName

method Main() {
  print D.y;
}

