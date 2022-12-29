// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Result<T> = Failure(error: string) | Success(value: T)
datatype ResultN<T(!new)> = Failure(error: string) | Success(value: T)

class C {}

method m() {
  var x1: Result<int>;
  var x2: ResultN<int>;
  var x3: Result<C>;
  var x4: ResultN<C>; // error
  var x5: Result<array<int>>;
  var x6: ResultN<array<int>>; // error
}

class D<T(==)> {}
codatatype E = Nil

method n(d: D<int>) {}
method n2(d: D<int->int>) {} // error: function types are not (==)
method n3(d: D<E>) {} // error: codataypes are not (==)
ghost method g2(d: D<int->int>) {}
ghost method g3(d: D<E>) {}

function g<T(==)>(t: T): T { // Warning: unnecessary (==)
  t
}

function gx<T>(t: T): T {
  t
}

function method gg<T(==)>(t: T): T {
  t
}

function method ggx<T>(t: T): T {
  t
}

method mm<T(==)>(t: T) {
  ghost var x := g(t);
  ghost var xx := gx(t);
  var y := gg(t);
  var yy := ggx(t);
}

method mx<T>(t: T) {
  ghost var x := g(t); // OK - g wants (==) but is ghost
  ghost var xx := gx(t); // OK ghost
  var y := gg(t); // error: gg wants (==)
  var yy := ggx(t);
}

ghost method mg<T(==)>(t: T) { // warning: unneccessary (==)
}


