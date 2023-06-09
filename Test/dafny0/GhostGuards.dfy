// RUN: %dafny /compile:3 /printTooltips /rprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Dt = Green | Dog

method Main()
{
  var x: bool;
  ghost var g: bool;

  if x {
  } else if g {  // ghost if
  } else if x {
  } else if g {
  } else {
  }

  if {  // ghost if
    case true =>
    case x =>
      if {
        case x =>
        case g =>
      }
    case g =>
  }

  while g  // ghost while
    decreases g
  {
    while
      decreases g
    {
      case false =>
      case g =>  g := false;
    }
    g := false;
  }
  g := *;

  while  // ghost while
    decreases g
  {
    case false =>
    case g =>  g := false;
  }

  var d: Dt;
  ghost var h: Dt;
  match d {
    case Green =>
    case Dog =>
  }
  match h {  // ghost match
    case Green =>
    case Dog =>
  }
}
