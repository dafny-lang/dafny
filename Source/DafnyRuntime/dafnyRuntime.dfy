module dafny {


datatype Tuple4<+T0,+T1,+T2,+T3> = Tuple4(0: T0, 1: T1, 2: T2, 3: T3)

}


method Main() {
  var t := (1,2,3,4);
}