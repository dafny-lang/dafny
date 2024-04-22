// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
    var f: int
}

method IsAllocated()
{
    var c := new C;
    var f := old(c.f);
}
