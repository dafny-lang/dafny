// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Block<Hash,Transaction,VProof> =
  Block(prevBlockHash:Hash, txs:seq<Transaction>, proof:VProof)

function GenesisBlock() : Block<int,int,int> {
  Block(0, [], 0)
}

method IsGenesisBlock(b : Block<int,int,int>) returns (eq : bool)
  ensures eq <==> b == GenesisBlock()
{
  var gb := GenesisBlock();
  eq := b == gb;
}

method Main() {
  var b := GenesisBlock();
  var eq := IsGenesisBlock(b);
  assert eq;
  print eq, "\n";
  TestEq();
}

newtype nt = int
newtype ntNative = x | -100 <= x < 100
class MyClass { var u: int }
datatype X = X(bool, char, int, real, nt, ntNative, bv8, bv167, ORDINAL, MyClass)

predicate TestAny<G(==)>(a: G, b: G)
  requires a == b
{
  a == b
}

method TestEq()
{
  print true == true, " ", TestAny(true, true), "\n";
  print 'e' == 'e', " ", TestAny('e', 'e'), "\n";
  print 12 == 12, " ", TestAny(12, 12), "\n";
  print 37.5 == 37.5, " ", TestAny(37.5, 37.5), "\n";
  var m0: nt, m1: nt := 12, 12;
  print m0 == m1, " ", TestAny(m0, m1), "\n";
  var n0: ntNative, n1: ntNative := 12, 12;
  print n0 == n1, " ", TestAny(n0, n1), "\n";
  var b0: bv8, b1: bv8 := 12, 12;
  print b0 == b1, " ", TestAny(b0, b1), "\n";
  var c0: bv167, c1: bv167 := 12, 12;
  print c0 == c1, " ", TestAny(c0, c1), "\n";
  var o0: ORDINAL, o1: ORDINAL := 12, 12;
  print o0 == o1, "\n";
  var obj := new MyClass;
  print obj == obj, " ", TestAny(obj, obj), "\n";

  var x0 := X(true, 'e', 12, 37.5, 12, 12, 12, 12, 12, obj);
  var x1 := X(true, 'e', 12, 37.5, 12, 12, 12, 12, 12, obj);
  print [x0] == [x1], " ", TestAny([x0], [x1]), "\n";
  print {x0} == {x1}, " ", TestAny({x0}, {x1}), "\n";
  print multiset{x0} == multiset{x1}, " ", TestAny(multiset{x0}, multiset{x1}), "\n";
  print map[x0 := n0] == map[x0 := n1], " ", TestAny(map[x0 := n0], map[x0 := n1]), "\n";
}
