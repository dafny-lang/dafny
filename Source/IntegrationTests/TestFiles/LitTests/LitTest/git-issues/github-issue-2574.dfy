// RUN: %exits-with 4 %baredafny verify --use-basename-for-filename "%s" > "%t.raw"
// RUN: %sed 's/^.*[\/\\]//' "%t".raw > "%t"
// RUN: %diff %s.expect %t
module Spec {
  type input
  method ReadInput() returns (i:input)
}

module Impl refines Spec {
  class input {}
  method ReadInput() returns (i:input) {
  }
}
