// RUN: %dafny /compileTarget:cs "%s" > "%t"
// RUN: dotnet CompileRunQuietly.dll >> "%t"

// RUN: %dafny /compileTarget:js "%s" >> "%t"
// RUN: node CompileRunQuietly.js >> "%t"

// RUN: %dafny /compileTarget:go "%s" >> "%t"
// RUN: ./CompileRunQuietly >> "%t"

// RUN: %dafny /compileTarget:java "%s" >> "%t"
// RUN: java CompileRunQuietly >> "%t"

// RUN: %diff "%s.expect" "%t"

/* In the future (when we've figured out how to obtain the right version of g++ on github),
 * C++ can be added by including these commands above:
 *
 *     %dafny /compileTarget:cpp "%s" >> "%t"
 *     ./CompileRunQuietly.exe >> "%t"
 *
 * and adding "g++" to lit.local.cfg in this folder.
 */

method Main() {
  print "hello, Dafny\n";
}
