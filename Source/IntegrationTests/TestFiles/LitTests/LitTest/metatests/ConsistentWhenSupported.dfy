
// Old way:

// RUN: %exits-with 0 %verify "%s" > "%t"
// RUN: %exits-with 0 %run --no-verify --target cs "%s" >> "%t"
// RUN: %exits-with 0 %run --no-verify --target js "%s" >> "%t"
// RUN: %exits-with 0 %run --no-verify --target go "%s" >> "%t"
// RUN: %exits-with 3 %run --no-verify --target java "%s" >> "%t"
// RUN: %exits-with 3 %run --no-verify --target cpp "%s" >> "%t"
// RUN: %exits-with 0 %run --no-verify --target py "%s" >> "%t"
// RUN: %diff "%s.oldway.expect" "%t"

// New way:

// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

iterator EmptyIterator() yields (r: bool) 
  ensures false
{}

method Main() {
  var i := new EmptyIterator();
  var more := i.MoveNext();
  expect !more;
  print "All done iterating!\n";
}
