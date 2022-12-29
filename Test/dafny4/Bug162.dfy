// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method foo<T(==)>(x:T)

datatype A = A(s:iset<int>)
datatype B = B(s:set<int>)
datatype C = C(s:imap<int,int>)
datatype D = D(s:map<int,int>)

method bar()
{
    var a:A;
    foo(a);

    var b:B;
    foo(b);

    var c:C;
    foo(c);

    var d:D;
    foo(d);

    var s:iset<int>;
    foo(s);

    var s':imap<int,int>;
    foo(s');
}
