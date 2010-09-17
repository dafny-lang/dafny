method MirrorImage<T>(m: array2<T>)
  requires m != null;
  modifies m;
  ensures (forall i,j :: 0 <= i && i < m.Length0 && 0 <= j && j < m.Length1 ==>
            m[i,j] == old(m[i, m.Length1-1-j]));
{
  var a := 0;
  while (a < m.Length0)
    invariant a <= m.Length0;
    invariant (forall i,j :: 0 <= i && i < a && 0 <= j && j < m.Length1 ==>
                m[i,j] == old(m[i, m.Length1-1-j]));
    invariant (forall i,j :: a <= i && i < m.Length0 && 0 <= j && j < m.Length1 ==>
                m[i,j] == old(m[i,j]));
  {
    var b := 0;
    while (b < m.Length1 / 2)
      invariant  b <= m.Length1 / 2;
      invariant (forall i,j :: 0 <= i && i < a && 0 <= j && j < m.Length1 ==>
                  m[i,j] == old(m[i, m.Length1-1-j]));
      invariant (forall j :: 0 <= j && j < b ==>
                  m[a,j] == old(m[a, m.Length1-1-j]) &&
                  old(m[a,j]) == m[a, m.Length1-1-j]);
      invariant (forall j :: b <= j && j < m.Length1-b ==> m[a,j] == old(m[a,j]));
      invariant (forall i,j :: a+1 <= i && i < m.Length0 && 0 <= j && j < m.Length1 ==>
                  m[i,j] == old(m[i,j]));
    {
      var tmp := m[a, m.Length1-1-b];
      m[a, m.Length1-1-b] := m[a, b];
      m[a, b] := tmp;
      b := b + 1;
    }
    a := a + 1;
  }
}

method Flip<T>(m: array2<T>)
  requires m != null && m.Length0 == m.Length1;
  modifies m;
  ensures (forall i,j :: 0 <= i && i < m.Length0 && 0 <= j && j < m.Length1 ==> m[i,j] == old(m[j,i]));
{
  var N := m.Length0;
  var a := 0;
  var b := 0;
  while (a != N)
    invariant a <= b && b <= N;
    invariant (forall i,j :: 0 <= i && i <= j && j < N ==>
                (if i < a || (i == a && j < b)
                  then m[i,j] == old(m[j,i]) && m[j,i] == old(m[i,j])
                  else m[i,j] == old(m[i,j]) && m[j,i] == old(m[j,i])));
    decreases N-a, N-b;
  {
    if (b < N) {
      var tmp := m[a,b];  m[a,b] := m[b,a];  m[b,a] := tmp;
      b := b + 1;
    } else {
      a := a + 1;  b := a;
    }
  }
}
