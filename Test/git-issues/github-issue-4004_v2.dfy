// RUN: %baredafny translate cs %args %s > %t
// RUN: %diff "%s.expect" "%t"

method Main() returns ()
{
  match (-19 / 23) {
    case 26 => {
      var v_bool_7: bool, v_bool_8: bool := (match true {
        case _ => true
      }), false;
    }
    case _ => {
    }
  }
}