// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Option<T> = None | Some(t:T)

class C {
  method m(x: Option<bool>) {
    var a := match x { case Some(true) => false case _ => true };
  }
}

class D<T> {
  method mm(x: Option<int>) {
    var b := match x { case Some(5) => false case _ => true };
  }
}

