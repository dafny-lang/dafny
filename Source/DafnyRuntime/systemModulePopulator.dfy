
method HasTuples() {
  var has0 := ();
  var has1 := (1, ghost 1.5);  // Just (1) is an int in parentheses instead
  var has2 := (1,2);
  var has3 := (1,2,3);
  var has4 := (1,2,3,4);
  var has5 := (1,2,3,4,5);
  var has6 := (1,2,3,4,5,6);
  var has7 := (1,2,3,4,5,6,7);
  var has8 := (1,2,3,4,5,6,7,8);
  var has9 := (1,2,3,4,5,6,7,8,9);
  var has10 := (1,2,3,4,5,6,7,8,9,10);
  var has11 := (1,2,3,4,5,6,7,8,9,10,11);
  var has12 := (1,2,3,4,5,6,7,8,9,10,11,12);
  var has13 := (1,2,3,4,5,6,7,8,9,10,11,12,13);
  var has14 := (1,2,3,4,5,6,7,8,9,10,11,12,13,14);
  var has15 := (1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  var has16 := (1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16);
  var has17 := (1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17);
  var has18 := (1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18);
  var has19 := (1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19);
  var has20 := (1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20);
}

method HasArrows() {
  var has0 := () => 42;
  var has1 := (x1: int) => 42;
  var has2 := (x1: int, x2: int) => 42;
  var has3 := (x1: int, x2: int, x3: int) => 42;
  var has4 := (x1: int, x2: int, x3: int, x4: int) => 42;
  var has5 := (x1: int, x2: int, x3: int, x4: int, x5: int) => 42;
  var has6 := (x1: int, x2: int, x3: int, x4: int, x5: int, x6: int) => 42;
  var has7 := (x1: int, x2: int, x3: int, x4: int, x5: int, x6: int, x7: int) => 42;
  var has8 := (x1: int, x2: int, x3: int, x4: int, x5: int, x6: int, x7: int, x8: int) => 42;
  var has9 := (x1: int, x2: int, x3: int, x4: int, x5: int, x6: int, x7: int, x8: int, x9: int) => 42;
  var has10 := (x1: int, x2: int, x3: int, x4: int, x5: int, x6: int, x7: int, x8: int, x9: int, x10: int) => 42;
  var has11 := (x1: int, x2: int, x3: int, x4: int, x5: int, x6: int, x7: int, x8: int, x9: int, x10: int, x11: int) => 42;
  var has12 := (x1: int, x2: int, x3: int, x4: int, x5: int, x6: int, x7: int, x8: int, x9: int, x10: int, x11: int, x12: int) => 42;
  var has13 := (x1: int, x2: int, x3: int, x4: int, x5: int, x6: int, x7: int, x8: int, x9: int, x10: int, x11: int, x12: int, x13: int) => 42;
  var has14 := (x1: int, x2: int, x3: int, x4: int, x5: int, x6: int, x7: int, x8: int, x9: int, x10: int, x11: int, x12: int, x13: int, x14: int) => 42;
  var has15 := (x1: int, x2: int, x3: int, x4: int, x5: int, x6: int, x7: int, x8: int, x9: int, x10: int, x11: int, x12: int, x13: int, x14: int, x15: int) => 42;
  var has16 := (x1: int, x2: int, x3: int, x4: int, x5: int, x6: int, x7: int, x8: int, x9: int, x10: int, x11: int, x12: int, x13: int, x14: int, x15: int, x16: int) => 42;
  // var has17 := (x1: int, x2: int, x3: int, x4: int, x5: int, x6: int, x7: int, x8: int, x9: int, x10: int, x11: int, x12: int, x13: int, x14: int, x15: int, x16: int, x17: int) => 42;
  // var has18 := (x1: int, x2: int, x3: int, x4: int, x5: int, x6: int, x7: int, x8: int, x9: int, x10: int, x11: int, x12: int, x13: int, x14: int, x15: int, x16: int, x17: int, x18: int) => 42;
  // var has19 := (x1: int, x2: int, x3: int, x4: int, x5: int, x6: int, x7: int, x8: int, x9: int, x10: int, x11: int, x12: int, x13: int, x14: int, x15: int, x16: int, x17: int, x18: int, x19: int) => 42;
  // var has20 := (x1: int, x2: int, x3: int, x4: int, x5: int, x6: int, x7: int, x8: int, x9: int, x10: int, x11: int, x12: int, x13: int, x14: int, x15: int, x16: int, x17: int, x18: int, x19: int, x20: int) => 42;
}

method HasArrays() {
  var has1 := new int[1];
  var has2 := new int[1,2];
  var has3 := new int[1,2,3];
  var has4 := new int[1,2,3,4];
  var has5 := new int[1,2,3,4,5];
  var has6 := new int[1,2,3,4,5,6];
  var has7 := new int[1,2,3,4,5,6,7];
  var has8 := new int[1,2,3,4,5,6,7,8];
  var has9 := new int[1,2,3,4,5,6,7,8,9];
  var has10 := new int[1,2,3,4,5,6,7,8,9,10];
  var has11 := new int[1,2,3,4,5,6,7,8,9,10,11];
  var has12 := new int[1,2,3,4,5,6,7,8,9,10,11,12];
  var has13 := new int[1,2,3,4,5,6,7,8,9,10,11,12,13];
  var has14 := new int[1,2,3,4,5,6,7,8,9,10,11,12,13,14];
  var has15 := new int[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15];
  var has16 := new int[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16];
  // var has17 := new int[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17];
  // var has18 := new int[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18];
  // var has19 := new int[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
  // var has20 := new int[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20];
}