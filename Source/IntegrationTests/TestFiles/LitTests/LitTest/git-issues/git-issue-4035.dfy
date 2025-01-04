// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


module ConstInTrait {
  type ReallyEmpty = x: int | false witness *

  trait UnimplementableTrait extends object {
    const x: ReallyEmpty
  }

  method M(o: object)
    ensures false // error
  {
    if o is UnimplementableTrait {
      var u := o as UnimplementableTrait;
      var r := u.x as ReallyEmpty; // this once allowed M to derive "false"
    }
  }
}

module VarInTrait {
  type ReallyEmpty = x: int | false witness *

  trait UnimplementableTrait extends object {
    var x: ReallyEmpty
  }

  method M(o: object)
    ensures false // error
  {
    if o is UnimplementableTrait {
      var u := o as UnimplementableTrait;
      var r := u.x as ReallyEmpty;
    }
  }
}

module ConstInClass {
  type ReallyEmpty = x: int | false witness *

  class UninstantiableClass {
    const x: ReallyEmpty

    constructor ()
      requires false
    {
    }
  }

  method M(o: object)
    ensures false // error
  {
    if o is UninstantiableClass {
      var u := o as UninstantiableClass;
      var r := u.x as ReallyEmpty; // this once allowed M to derive "false"
    }
  }
}

module VarInClass {
  type ReallyEmpty = x: int | false witness *

  class UninstantiableClass extends object {
    var x: ReallyEmpty

    constructor ()
      requires false
    {
    }
  }

  method M(o: object)
    ensures false // error
  {
    if o is UninstantiableClass {
      var u := o as UninstantiableClass;
      var r := u.x as ReallyEmpty;
    }
  }
}
