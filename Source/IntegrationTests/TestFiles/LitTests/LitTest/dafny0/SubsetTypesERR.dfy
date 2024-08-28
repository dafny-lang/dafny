// RUN: %exits-with 4 %verify --relax-definite-assignment "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module AssignmentsFromNewAllocation {
  // Many of the tests in this module are regression tests
  class Person { }
  class Cell<T> { }

  method K(p: Person) returns (a: array<Person?>, b: array<Person>) {
    if * {
      a := new Person[0];  // error: cannot assign array<Person> to array<Person?>
    } else if * {
      a := new Person[100](_ => p);  // error: ditto
    } else if * {
      a := new Person[] [p, p];  // error: ditto
    } else if * {
      a := b;  // error: ditto
    }
  }

  method L(p: Person) returns (a: array<Person?>, b: array<Person>) {
    if * {
      b := new Person?[100];  // error: cannot assign array<Person?> to array<Person>
    } else if * {
      b := new Person?[100](_ => p);  // error: ditto
    } else if * {
      b := new Person?[] [p, p];  // error: ditto
    } else if * {
      b := a;  // error: ditto
    }
  }

  method M(N: nat, p: Person) {
    var a: array<Person?>;
    var b: array<Person>;
    if * {
      a := b;  // error
    } else if * {
      b := a;  // error
    } else if * {
      a := new Person?[N](_ => p);
      b := a;  // error
    } else if * {
      a := new Person[N](_ => p);  // error: cannot assign array<Person> to array<Person?>
    } else if * {
      b := new Person?[N](_ => p);  // error: cannot assign array<Person?> to array<Person>
    }
  }

  method P(cc: Cell<Person?>, dd: Cell<Person>)
  {
    var c: Cell<Person?>;
    var d: Cell<Person>;
    if * {
      c := new Cell<Person?>;
    } else if * {
      d := new Cell<Person?>;  // error: Cell<Person?> is not assignable to Cell<Person>
    } else if * {
      c := new Cell<Person>;  // error: Cell<Person> is not assignable to Cell<Person?>
    } else if * {
      d := new Cell<Person>;
    } else if * {
      c := dd;  // error: Cell<Person> is not assignable to Cell<Person?>
    } else if * {
      d := cc;  // error: Cell<Person?> is not assignable to Cell<Person>
    }
  }
}
