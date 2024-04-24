// RUN: %verify %s > %t
// RUN: %diff "%s.expect" "%t"

class C_2 {
  var F_C_2_real_1: real
  var F_C_2_real_2: real
  var F_C_2_real_3: real
  var F_C_2_bool_4: bool
  var F_C_2_real_5: real
  var F_C_2_bool_6: bool
  constructor (F_C_2_real_1: real, F_C_2_real_2: real, F_C_2_real_3: real, F_C_2_bool_4: bool, F_C_2_real_5: real, F_C_2_bool_6: bool) {
    this.F_C_2_real_1 := F_C_2_real_1;
    this.F_C_2_real_2 := F_C_2_real_2;
    this.F_C_2_real_3 := F_C_2_real_3;
    this.F_C_2_bool_4 := F_C_2_bool_4;
    this.F_C_2_real_5 := F_C_2_real_5;
    this.F_C_2_bool_6 := F_C_2_bool_6;
  }
}

method Main() returns ()
{
  var v_int_7: int := 0;
  var v_int_8: int := 1;
  while (v_int_7 < v_int_8)
  {
    v_int_7 := (v_int_7 + 1);
    var v_C_2_1: C_2 := new C_2(-20.01, -22.48, -8.26, false, -5.90, false);
    match 0 {
      case _ => {
        if false {
          continue;
        } else {
          var v_C_2_8: C_2 := new C_2(-28.38, -28.94, 9.05, (2) is int, 0.35, v_C_2_1.F_C_2_bool_6);
        }
      }
    }
  }
}
