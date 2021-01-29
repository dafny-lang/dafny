// RUN: %dafny /compileVerbose:1 /compileTarget:cs "%s" > "%t"
// RUN: dotnet CompileAndThenRun.dll >> "%t"

// RUN: %dafny /compileVerbose:1 /compileTarget:js "%s" >> "%t"
// RUN: node CompileAndThenRun.js >> "%t"

// RUN: %dafny /compileVerbose:1 /compileTarget:go "%s" >> "%t"
// RUN: ./CompileAndThenRun >> "%t"

// RUN: %dafny /compileVerbose:1 /compileTarget:java "%s" >> "%t"
// RUN: java CompileAndThenRun >> "%t"

// RUN: %diff "%s.expect" "%t"

/* In the future (when we've figured out how to obtain the right version of g++ on github),
 * C++ can be added by including these commands above:
 *
 *     %dafny /compileVerbose:1 /compileTarget:cpp "%s" >> "%t"
 *     ./CompileAndThenRun.exe >> "%t"
 *
 * and adding "g++" to lit.local.cfg in this folder.
 */

method Main() {
  print "hello, Dafny\n";
}
