// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module AutoInitRegressions {
  trait Y { }

  datatype Datatype = Make
  {
    static const Static: Y  // error: Y is not auto-init
    const Instance: Y  // error: Y is not auto-init
  }

  method Main() {
    print Datatype.Static, "\n";
    var c := Make;
    print c.Instance, "\n";
  }

  const Global: Y  // error: Y is not auto-init

  class Class {  // error: InstanceField is of type Y, which is not auto-init, so class must have a constructor
    static const StaticField: Y  // error: Y is not auto-init
    const InstanceField: Y
  }

  trait Trait {
    static const StaticField: Y  // error: Y is not auto-init
    const InstanceField: Y
  }

  class TraitImpl extends Trait {  // error: inherited InstanceField is of type Y, which is not auto-init, so class must have a constructor
  }

  newtype Newtype = int
  {
    static const Static: Y  // error: Y is not auto-init
    const Instance: Y  // error: Y is not auto-init
  }

  type Opaque
  {
    static const Static: Y  // error: Y is not auto-init
    const Instance: Y  // error: Y is not auto-init
  }
}

module NonemptyRegressions {
  type Y { }

  datatype Datatype = Make
  {
    ghost static const Static: Y  // error: Y is not nonempty
    ghost const Instance: Y  // error: Y is not nonempty
  }

  ghost const Global: Y  // error: Y is not nonempty

  class Class {  // error: InstanceField is of type Y, which is not nonempty, so class must have a constructor
    ghost static const StaticField: Y  // error: Y is not nonempty
    ghost const InstanceField: Y
  }

  trait Trait {
    ghost static const StaticField: Y  // error: Y is not nonempty
    ghost const InstanceField: Y
  }

  class TraitImpl extends Trait {  // error: inherited InstanceField is of type Y, which is not auto-init, so class must have a constructor
  }

  newtype Newtype = int
  {
    ghost static const Static: Y  // error: Y is not nonempty
    ghost const Instance: Y  // error: Y is not nonempty
  }

  type Opaque
  {
    ghost static const Static: Y  // error: Y is not nonempty
    ghost const Instance: Y  // error: Y is not nonempty
  }
}
