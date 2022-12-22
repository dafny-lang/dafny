// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module P {
  const c = 5
  method m() {
    var x = 5;
    var z := ( var y = 5; y);
  }
}
