method M(x: real)
  decreases x;
{
  if 0.0 <= x {
    M(x - 15.0);
  }
}

method N(x: real, y: real)
  decreases x, y;
{
  if 0.0 <= y {
    N(x, y - 1.0);
  } else if 0.0 <= x {
    N(x - 1.0, 300.0);
  }
}

method N_implicitDecreases(x: real, y: real)
{
  if 0.0 <= y {
    N_implicitDecreases(x, y - 1.0);
  } else if 0.0 <= x {
    N_implicitDecreases(x - 1.0, 300.0);
  }
}

method P(x: real)
  decreases x;
{
  if 0.0 <= x {
    P(x - 0.5);  // error: don't descease enough
  }
}

method Q(x: real)
  decreases 2.0 * x;
{
  if 0.0 <= x {
    Q(x - 0.5);  // fine
  }
}

method R(x: real)
  decreases x;
{
  R(x - 1.0);  // error: no lower bound
}

method W0(N: real)
{
  var i := 0.0;
  while i < N
    decreases N - i;
  {
    i := i + 1.0;
  }
}

method W1(N: real)
{
  var i := 0.0;
  while i < N
  {
    i := i + 1.0;
  }
}

method W2(N: real)
{
  var i, n := 0.0, N;
  while i < n
    decreases n - i;
  {
    if * {
      i := i + 1.0;
    } else {
      n := n - 1.0;
    }
  }
}

method W3(N: real)
{
  var i, n := 0.0, N;
  while i < n
  {
    if * {
      i := i + 1.0;
    } else {
      n := n - 1.0;
    }
  }
}

method W4(N: real)
{
  var i, n := 0.0, N;
  while i != n
    decreases if i < n then n - i else i - n;  // absolute value
  {
    if i < n {
      i := i + 1.0;
      if n < i { break; }
    } else {
      n := n + 1.0;
      if i < n { break; }
    }
  }
}

method W5(N: real)
{
  var i, n := 0.0, N;
  while i != n
  {
    if i < n {
      i := i + 1.0;
      if n < i { break; }
    } else {
      n := n + 1.0;
      if i < n { break; }
    }
  }
}
