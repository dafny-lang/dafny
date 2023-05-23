// RUN: %exits-with 4 %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function existential(mat: array2<bool>): bool
    reads mat
{
    exists i, j :: 0 <= i < mat.Length0 && 0 <= j < mat.Length1 && mat[i,j]
}

method foo(n: int) {
    var mat := new bool[n,n];
    forall i,j | (0 <= i < n && 0 <= j < n) {
        mat[i,j] := false;
    }
    var i := 0;
    while i < n {
        var j := 0;
        while j < n {
            mat[i,j] := true;
            j := j + 1;
        }
        i := i + 1;
    }
    assert !existential(mat);
}
