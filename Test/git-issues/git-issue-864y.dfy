// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module B {
  export B reveals *
  module A { const a := 30 }
  const A := 60
}

// This duplicate definition causes an inscrutable follow-on error in
// processing the export set. The 'reveals *' creates a list of
// ExportSignatures by name and whether they are revealable.
// But later those names are looked up in the list of declarations.
// When the const A is looked up, the declaration for the module A is
// found. The const A was marked as revealable, so the module A is
// reported as an error as it is not revealable.
// I tried a few simple fixes for this problem, but they all caused
// more problems than they solved, mostly because the 'reveals *' is
// translated into a list of names before most other processing is done
// that is, before resolution.
