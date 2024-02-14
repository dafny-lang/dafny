// RUN: %testDafnyForEachResolver "%s" -- --general-traits:datatype

trait Tr {
  function Decrease(): nat {
    0
  }

  function F(): nat
    decreases Decrease()
}

datatype Dt extends Tr = Dt { 
  function F(): nat
    decreases 0
  {
    0
  }
}
