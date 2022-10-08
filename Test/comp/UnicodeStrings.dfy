// RUN: %baredafny verify --unicode-char "%s" %args > "%t"
// RUN: %baredafny run --no-verify --unicode-char --target:cs "%s" %args >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main(args: seq<string>) {
  var trickyString := "Dafny is just so " + [0x1F60E as char];
  print trickyString, "\n";
}
