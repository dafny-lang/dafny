// RUN: %dafny /compileVerbose:1 /compileTarget:cs /compile:3 "%s" > "%t"
// RUN: %dafny /compileVerbose:1 /compileTarget:js /compile:3 "%s" >> "%t"
// RUN: %dafny /compileVerbose:1 /compileTarget:go /compile:3 "%s" >> "%t"
// RUN: %dafny /compileVerbose:1 /compileTarget:java /compile:3 "%s" >> "%t"
// RUN: %dafny /compileVerbose:1 /compileTarget:cpp /compile:3 "%s" >> "%t"
// RUN: %dafny /compileVerbose:1 /compileTarget:py /compile:3 "%s" >> "%t"
// RUN: %dafny /compileTarget:cs /compile:3 "%s" >> "%t"
// RUN: %dafny /compileTarget:js /compile:3 "%s" >> "%t"
// RUN: %dafny /compileTarget:go /compile:3 "%s" >> "%t"
// RUN: %dafny /compileTarget:java /compile:3 "%s" >> "%t"
// RUN: %dafny /compileTarget:cpp /compile:3 "%s" >> "%t"
// RUN: %dafny /compileTarget:py /compile:3 "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
