
method test(x:seq<int>) 
    requires |x| == 10;
{
    var elts := x[4:2:3];
    var a, b, c := elts[0], elts[1], elts[2];

    assert |a| == 4;
    assert |b| == 2;
    assert |c| == 3;

    assert forall i :: 0 <= i < |a| ==> a[i] == x[i];
    assert forall i :: 0 <= i < |b| ==> b[i] == x[i+4];
    assert forall i :: 0 <= i < |c| ==> c[i] == x[i+6];

    var elts2 := x[1:5:];  // Leaving off the last length puts the remaining elements in the last seq
    var d, e, f := elts2[0], elts2[1], elts2[2];
    assert |d| == 1;
    assert |e| == 5;
    assert |f| == |x| - (|d| + |e|);

    assert forall i :: 0 <= i < |d| ==> d[i] == x[i];
    assert forall i :: 0 <= i < |e| ==> e[i] == x[i+1];
    assert forall i :: 0 <= i < |f| ==> f[i] == x[i+6];
}
