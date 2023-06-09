// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run --no-verify --target=cs   %args "%s" >> "%t"
// RUN: %baredafny run --no-verify --target=js   %args "%s" >> "%t"
// RUN: %baredafny run --no-verify --target=go   %args "%s" >> "%t"
// RUN: %baredafny run --no-verify --target=py   %args "%s" >> "%t"
// RUN: %baredafny run --no-verify --target=java %args "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  // This works fine in all languages because € is a single UTF-16 code unit.
  print "Euro sign: " + [0x20AC as char], "\n"; // €

  // Unfortunately, the following does *not* work in all languages: some of our
  // compilers don't correctly handle paired UTF-16 code units (e.g. Go)
  // print "Emoji: " + [0xD83D as char, 0xDE14 as char], "\n"; // 😔
}
