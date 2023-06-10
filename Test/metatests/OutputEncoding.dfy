// RUN: %testDafnyForEachCompiler "%s"

method Main() {
  // This works fine in all languages because € is a single UTF-16 code unit.
  print "Euro sign: " + [0x20AC as char], "\n"; // €

  // Unfortunately, the following does *not* work in all languages: some of our
  // compilers don't correctly handle paired UTF-16 code units (e.g. Go)
  // print "Emoji: " + [0xD83D as char, 0xDE14 as char], "\n"; // 😔
}
