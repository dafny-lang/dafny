// RUN: %verify "%s" --warn-contradictory-assumptions
abstract module Digit {
  function BASE(): nat
    ensures BASE() > 1

  type digit = i: nat | 0 <= i < BASE()
}

module M refines Digit {
    function BASE(): nat { 32 }
}
