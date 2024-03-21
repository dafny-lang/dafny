// RUN: %verify --progress --isolate-assertions --cores=1 %s > %t.raw
// RUN: %sed 's/time: \d*//g' "%t".raw > "%t
// RUN: %diff "%s.expect" "%t"

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