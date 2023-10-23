// RUN: %baredafny verify %args %s > %t
// RUN: %diff "%s.expect" "%t"

method Main() returns ()
{
  match 8 {
    case _ => {
      var v_bool: bool, v_real: real := true, match 15.06 {
        case _ => 6.58
      };
      print v_bool, " ", v_real, "\n";
    }
  }
}