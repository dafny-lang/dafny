// RUN: %dafny  /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Block<Hash,Transaction,VProof> = 
  Block(prevBlockHash:Hash, txs:seq<Transaction>, proof:VProof)

function method GenesisBlock() : Block<int,int,int> {
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
}
