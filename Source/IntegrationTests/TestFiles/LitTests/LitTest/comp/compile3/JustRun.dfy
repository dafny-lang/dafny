// NONUNIFORM: /compileVerbose:1 output is backend sensitive
// (although the second set of comamnds could be separated out)
// RUN: %run --target cs --unicode-char false --verbose "%s" > "%t"
// RUN: %run --target js --unicode-char false --verbose "%s" >> "%t"
// RUN: %run --target go --unicode-char false --verbose "%s" >> "%t"
// RUN: %run --target java --unicode-char false --verbose "%s" >> "%t"
// RUN: %run --target cpp --unicode-char false --verbose "%s" >> "%t"
// RUN: %run --target py --unicode-char false --verbose "%s" >> "%t"
// RUN: %run --target cs --unicode-char false "%s" >> "%t"
// RUN: %run --target js --unicode-char false "%s" >> "%t"
// RUN: %run --target go --unicode-char false "%s" >> "%t"
// RUN: %run --target java --unicode-char false "%s" >> "%t"
// RUN: %run --target cpp --unicode-char false "%s" >> "%t"
// RUN: %run --target py --unicode-char false "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Dafny\n";
}
