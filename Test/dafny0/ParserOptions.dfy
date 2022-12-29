// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This module tests support for the `:options` attribute

// Use legacy syntax
module {:options "/functionSyntax:3"} FunctionMethodSyntax {
  function method CompiledFunction() : int { 1 }
  function GhostFunction() : int { 1 }
}

// Use new syntax
module {:options "/functionSyntax:4"} GhostFunctionSyntax {
  function CompiledFunction() : int { 1 }
  ghost function GhostFunction() : int { 1 }
}

// Check that later :options take precedence
module {:options "/functionSyntax:3"} {:options "/functionSyntax:4"}
  StillGhostFunctionSyntax
{
  function CompiledFunction() : int { 1 }
  ghost function GhostFunction() : int { 1 }
}

// Check that options are correctly reset
module BackToDefault {
  function method CompiledFunction() : int { 1 }
  function GhostFunction() : int { 1 }
}

// Sanity check
method Main() {
  print FunctionMethodSyntax.CompiledFunction()
      + GhostFunctionSyntax.CompiledFunction()
      + StillGhostFunctionSyntax.CompiledFunction()
      + BackToDefault.CompiledFunction();
}
