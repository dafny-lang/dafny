// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --spill-translation --allow-deprecation --unicode-char false

newtype u32 = i: int | 0 <= i < 0x100000000

codatatype Stream = Cons(head: u32, tail: Stream)

function Ones(): Stream { Cons(1, Ones()) }

method Main() {
  print Ones().head, "\n";
}
