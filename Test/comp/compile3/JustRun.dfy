// RUN: %dafny /unicodeChar:0 /compileVerbose:1 /compileTarget:cs /compile:3 "%s" > "%t"
// RUN: %dafny /unicodeChar:0 /compileVerbose:1 /compileTarget:js /compile:3 "%s" >> "%t"
// RUN: %dafny /unicodeChar:0 /compileVerbose:1 /compileTarget:go /compile:3 "%s" >> "%t"
// RUN: %dafny /unicodeChar:0 /compileVerbose:1 /compileTarget:java /compile:3 "%s" >> "%t"
// RUN: %dafny /unicodeChar:0 /compileVerbose:1 /compileTarget:cpp /compile:3 "%s" >> "%t"
// RUN: %dafny /unicodeChar:0 /compileVerbose:1 /compileTarget:py /compile:3 "%s" >> "%t"
// RUN: %dafny /unicodeChar:0 /compileTarget:cs /compile:3 "%s" >> "%t"
// RUN: %dafny /unicodeChar:0 /compileTarget:js /compile:3 "%s" >> "%t"
// RUN: %dafny /unicodeChar:0 /compileTarget:go /compile:3 "%s" >> "%t"
// RUN: %dafny /unicodeChar:0 /compileTarget:java /compile:3 "%s" >> "%t"
// RUN: %dafny /unicodeChar:0 /compileTarget:cpp /compile:3 "%s" >> "%t"
// RUN: %dafny /unicodeChar:0 /compileTarget:py /compile:3 "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
