// RUN: %dafny /compileVerbose:1 /compileTarget:cs /compile:3 "%s" > "%t"
// RUN: %dafny /compileVerbose:1 /compileTarget:js /compile:3 "%s" >> "%t"
// RUN: %dafny /compileVerbose:1 /compileTarget:go /compile:3 "%s" >> "%t"
// RUN: %dafny /compileVerbose:1 /compileTarget:java /compile:3 "%s" >> "%t"
// RUN: %dafny /compileTarget:cs /compile:3 "%s" >> "%t"
// RUN: %dafny /compileTarget:js /compile:3 "%s" >> "%t"
// RUN: %dafny /compileTarget:go /compile:3 "%s" >> "%t"
// RUN: %dafny /compileTarget:java /compile:3 "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

/* In the future (when we've figured out how to obtain the right version of g++ on github),
 * C++ can be added by including these commands above:
 *
 *     %dafny /compileVerbose:1 /compileTarget:cpp /compile:3 "%s" >> "%t"
 * ...
 *     %dafny /compileTarget:cpp /compile:3 "%s" >> "%t"
 *
 */

method Main() {
  print "hello, Dafny\n";
}
