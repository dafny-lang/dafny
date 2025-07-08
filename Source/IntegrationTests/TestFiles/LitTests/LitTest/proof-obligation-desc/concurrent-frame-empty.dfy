// RUN: %exits-with 4 %verify --show-proof-obligation-expressions --reads-clauses-on-methods "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C<T> {}

function {:concurrent} ReadsEmpty<T>(c: C<T>): bool
    reads {c}
{
    true
}

method {:concurrent} ModifiesEmpty<T>(c: C<T>)
    reads {}
    modifies {c}
{}
