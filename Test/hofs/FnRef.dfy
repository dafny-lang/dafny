// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


class Ref<A(0)> {
  var val: A
}

method Nope() {
  var f : Ref<int ~> bool>;
  var g : int ~> bool;

  f := new Ref<int ~> bool>;

  f.val := x => true;

  g := x reads f reads f.val.reads(x) => !f.val(x);
}

method M() {
  var f : Ref<int ~> bool>;
  var g : int ~> bool;

  f := new Ref<int ~> bool>;

  f.val := x => true;

  g := x reads f reads f.val.reads(x) requires f.val.requires(x) => !f.val(x);

  f.val := g;

  if (!g(0)) {
    assert !g(0);
  } else {
    assert g(0);
  }
}


method L() {
  var f : Ref<() ~> bool>;
  f := new Ref<() ~> bool>;
  f.val := () reads f reads f.val.reads() requires !f.val.requires() => true;

  if (f.val.requires()) {
    assert !f.val.requires();
  } else {
    assert f.val.requires();
  }
}

method LRead() {
  var o : object?;
  var f : Ref<() ~> bool>;
  f := new Ref<() ~> bool>;
  f.val := () reads f
              reads f.val.reads()
              reads if o in f.val.reads() then {} else {o}
              => true;

  assume o != null;
  assert o != f;

  if (o in f.val.reads()) {
    assert o !in f.val.reads();
  } else {
    assert o in f.val.reads();
  }
}

