// NONUNIFORM: /compileVerbose:1 output is backend sensitive
// (although the second set of comamnds could be separated out)
// RUN: %run --target cs --verbose "%s" > "%t"
// RUN: %run --target js --verbose "%s" >> "%t"
// RUN: %run --target go --verbose "%s" >> "%t"
// RUN: %run --target java --verbose "%s" >> "%t"
// RUN: %run --target cpp --unicode-char false --verbose "%s" >> "%t"
// RUN: %run --target py --verbose "%s" >> "%t"
// RUN: %run --target cs "%s" >> "%t"
// RUN: %run --target js "%s" >> "%t"
// RUN: %run --target go "%s" >> "%t"
// RUN: %run --target java "%s" >> "%t"
// RUN: %run --target cpp --unicode-char false "%s" >> "%t"
// RUN: %run --target py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
