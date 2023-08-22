include "AST/Formatting.dfy"
include "Verifier/AlcorEngine.dfy"

module EnsureNoRemoval {
  import opened Alcor
  
  method DebugTest() {
    var _ := Debug("hello");
  }
}