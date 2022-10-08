// RUN: %baredafny verify --unicode-char "%s" %args > "%t"
// RUN: %baredafny run --no-verify --unicode-char --target:cs "%s" %args >> "%t"
// RUN: %diff "%s.expect" "%t"

newtype uint32 = x: int | 0 <= x < 0x1_0000_0000
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method Main(args: seq<string>) {
  var trickyString := "Dafny is just so " + [0x1F60E as char];
  print trickyString, "\n";

  var s := "Ceci n'est pas une string";
  var notAString := seq(|s|, i requires 0 <= i < |s| => s[i] as int32);
  print notAString, "\n";
}
