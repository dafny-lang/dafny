// NONUNIFORM: /compileVerbose:1 output is backend sensitive
// (although the second set of comamnds could be separated out)
// RUN: %run --unicode-char false --verbose --target cs "%s" > "%t"
// RUN: %run --unicode-char false --verbose --target js "%s" >> "%t"
// RUN: %run --unicode-char false --verbose --target go "%s" >> "%t"
// RUN: %run --unicode-char false --verbose --target java "%s" >> "%t"
// RUN: %run --unicode-char false --verbose --target cpp "%s" >> "%t"
// RUN: %run --unicode-char false --verbose --target py "%s" >> "%t"
// RUN: %run --unicode-char false --target cs "%s" >> "%t"
// RUN: %run --unicode-char false --target js "%s" >> "%t"
// RUN: %run --unicode-char false --target go "%s" >> "%t"
// RUN: %run --unicode-char false --target java "%s" >> "%t"
// RUN: %run --unicode-char false --target cpp "%s" >> "%t"
// RUN: %run --unicode-char false --target py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
