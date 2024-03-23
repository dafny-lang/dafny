// RUN: %testDafnyForEachCompiler "%s"
// RUN: %testDafnyForEachCompiler "%s" -- --unicode-char=false

method Main() {
  var s: seq<char>;
  s := *;
  print "(", s, ") ", s == "", " ", "" == s, " ", |s|, "\n";
  s := "";
  print "(", s, ") ", s == "", " ", "" == s, " ", |s|, "\n";
  s := "hello";
  print "(", s, ") ", s == "", " ", "" == s, " ", |s|, "\n";
}
