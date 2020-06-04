  class MyClass {
    ghost const repr : object
  }

  datatype D1 = D1(o : MyClass)
  {
    ghost const objs : set<object> := getObjs()

    function getObjs() : set<object>
      reads o
      { {o, o.repr} }
  }
