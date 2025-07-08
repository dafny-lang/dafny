// RUN: %exits-with 0 %run "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello";
}