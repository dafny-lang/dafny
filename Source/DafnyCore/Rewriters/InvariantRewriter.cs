using System;
using System.Linq;

namespace Microsoft.Dafny;

public class InvariantRewriter(ErrorReporter reporter) : IRewriter(reporter) {
  internal override void PreVerify(ModuleDefinition module) {
    foreach (var decl in module.TopLevelDecls) {
      if (decl is TopLevelDeclWithMembers cl) {
        ProcessTopLevelDecl(cl);
      }
    }
  }

  void ProcessTopLevelDecl(TopLevelDeclWithMembers cl) {
    // First, we need to grab the invariant
    Invariant invariant;
    try {
      invariant = (Invariant)cl.Members.First(member => member is Invariant);
    } catch (InvalidOperationException) {
      // No invariant, nothing to be done
      return;
    }
    
    foreach (var member in cl.Members) {
      // TODO(somayyas): can we give better error messages here?
      // e.g., instead of "postcondition could not be proved" => "an invariant clause could not be proved"
      // "related location: this is the postcondition" => "this is the invariant clause"
      switch (member) {
        // Constructors have the invariant as additional ensures clauses
        case Constructor ctor:
          // See below why invariant clauses are added last
          ctor.Ens.AddRange(invariant.Body);
          break;
        // Currently, we assume that each method is public and, as such, needs to require/ensure the invariant
        case Method method:
          // Have to add the invariant at the front of the requires clauses, in case subsequent clauses depend on them
          // to be well-formed
          method.Req.InsertRange(0, invariant.Body);
          // Dually, the invariant is ensured last
          method.Ens.AddRange(invariant.Body);
          break;
        // Functions need only assume the invariant
        case Function function:
          function.Req.InsertRange(0, invariant.Body);
          break;
      }
    }
  }
}