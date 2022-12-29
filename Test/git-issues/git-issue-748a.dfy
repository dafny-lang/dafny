// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method ok() {
  var array0: int := 10;
  var array1: int := 10;
  var array1?: int := 10;
  var array10z: int := 10;
  var bv01: int := 100;

  var y: array2;
  var z: array10;
  var b: bv0;
}

method badtypes() {
  var x: array0;
  var y: array1;
  var z: array1?;
}
