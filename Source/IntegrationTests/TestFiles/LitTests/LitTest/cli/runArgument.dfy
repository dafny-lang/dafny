// NONUNIFORM: This tests front-end behavior, and is back-end independent.
// RUN: %run %s blie 2 &> %t
// RUN: %run %s --blie --2 &>> %t
// RUN: %run %s -- --bla --2 &>> %t
// RUN: %diff "%s.expect" "%t"

method Main(args: seq<string>) {
  if |args| != 3 {
    print "Expected 3 arguments, got ", |args|;
  } else {
    print args[1], " says ";
    if args[2] == "1" {
      print "hello\n";
    } else if args[2] == "2" {
      print "howdy\n";
    } else {
      print args[2],"\n";
    }
  }
}