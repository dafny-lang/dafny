// A dotted module name: the synthesized parent "Outer" has no origin of its own, so the
// declaration that came from the .doo is one level down.
module Outer.Inner {
  function G(): int { 2 }
}
