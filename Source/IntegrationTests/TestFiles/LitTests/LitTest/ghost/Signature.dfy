// RUN: %testDafnyForEachResolver "%s" -- --print:-


// The following signature used to cause the error "Undeclared top-level type or type parameter: _tuple#2OG".
method Test(ghost c: (int, ghost (int, int)))
{
}
