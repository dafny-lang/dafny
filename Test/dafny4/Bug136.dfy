// RUN: %dafny /compile:0 /print:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method test()
{
    assume false;
    assert true;
}




