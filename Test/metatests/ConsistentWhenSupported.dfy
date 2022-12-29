
// Old way:

// RUN: %exits-with 0 %baredafny verify %args "%s" > "%t"
// RUN: %exits-with 0 %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %exits-with 0 %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %exits-with 0 %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %exits-with 3 %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /compileTarget:cpp "%s" >> "%t"
// RUN: %exits-with 0 %baredafny run %args --no-verify --target=py "%s" "%s" >> "%t"
// RUN: %diff "%s.oldway.expect" "%t"

// New way:

// RUN: %testDafnyForEachCompiler "%s"

iterator EmptyIterator() yields (r: bool) 
  ensures false
{}

method Main() {
  var i := new EmptyIterator();
  var more := i.MoveNext();
  expect !more;
  print "All done iterating!\n";
}
