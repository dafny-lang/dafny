method test0(x: int)
{
  ghost var {:assumption} a0 := false;  // error
  ghost var a1, {:assumption} a2 := true, false;  // error
  ghost var {:assumption} a3: bool;
  var {:assumption} a4;  // 2 errors

  a0 := a0 && (0 < x);

  a1 := a1 && true;

  a3 := true;  // error

  a3 := a2 && true;  // error

  a3 := a3 && true;
}


method test1()
{
  ghost var {:assumption} a0: bool;

  a0 := true;  // error

  a0 := a0 && true;

  a0 := a0 && true;  // error
}


method test2()
{
  ghost var {:assumption} a0: bool;

  a0 := a0 && true;

  if (false)
  {
    var a0 := 1;

    a0 := 2;

    a0 := 3;

    if (false)
    {
      ghost var {:assumption} a0: bool;

      a0 := a0;  // error

      if (false)
      {
        var {:assumption} a0: bool;  // error

        if (false)
        {
          ghost var {:assumption} a0 := 1;  // 2 errors

          if (false)
          {
            ghost var {:assumption} a0: bool;

            a0 := a0 && true;

            a0 := a0 && true;  // error
          }
        }
      }
    }
  }
}
