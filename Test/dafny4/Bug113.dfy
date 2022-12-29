// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype D = D(q:int, r:int, s:int, t:int)

method Main()
{
    print D(10, 20, 30, 40);
    print "\n";
}
