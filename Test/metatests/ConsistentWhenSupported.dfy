
// Old way:

// RUN: %exits-with 0 %dafny /compile:0 "%s" > "%t"
// RUN: %exits-with 0 %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %exits-with 0 %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %exits-with 0 %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /compileTarget:cpp "%s" >> "%t"
// RUN: %exits-with 0 %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t"
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
