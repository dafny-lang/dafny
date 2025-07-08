// RUN: %verify --cores=1 --progress Symbol --isolate-assertions %s > %t
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
