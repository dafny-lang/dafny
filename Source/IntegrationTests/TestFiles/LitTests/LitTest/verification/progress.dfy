// RUN: %verify --progress SymbolParts --isolate-assertions --cores=1 %s > %t
// RUN: %OutputCheck --file-to-check %t "%S/Inputs/progressFirstSequence.check"
// RUN: %OutputCheck --file-to-check %t "%S/Inputs/progressSecondSequence.check"


method Foo() 
{
  assert true;
  assert true; 
}

method Faz() ensures true { }

method Fopple() ensures true { }

method Burp() 
{
  assert true; 
  assert true;
}

method Blanc() ensures true { }
