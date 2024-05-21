// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method ForallLHSUniqueArray(a: array<int>)
    modifies a
{
    forall i | 0 <= i < a.Length {
        a[0] := i;
    }
}

method ForallLHSUniqueArray2(a: array2<int>)
    modifies a
{
    forall i, j | 0 <= i < a.Length0 && 0 <= j < a.Length1 {
        a[0, 0] := i + j;
    }
}

class C { var f: int }

method ForallLHSUniqueObj(a: array<C>)
    modifies a
    modifies set i | 0 <= i < a.Length :: a[i]`f
{
    forall i | 0 <= i < a.Length {
        a[i].f := i;
    }
}