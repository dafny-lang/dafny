// RUN: %dafny /compile:0 /unicodeChar:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /unicodeChar:0 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /unicodeChar:0 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /unicodeChar:0 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /unicodeChar:0 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /unicodeChar:0 /compileTarget:cpp "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /unicodeChar:0 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "XYZ"; // Checks that no extra newline is added to the output
}
