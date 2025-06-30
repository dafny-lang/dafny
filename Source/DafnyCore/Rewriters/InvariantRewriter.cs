using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class InvariantRewriter(Program program, ErrorReporter reporter) : IRewriter(reporter) {
  internal override void PreResolve(ModuleDefinition module) {
    foreach (var decl in module.TopLevelDecls) {
      if (decl is TopLevelDeclWithMembers cl) {
        PreResolveTopLevelDecl(cl);
      }
    }
  }
  
  // Add invariants as pre- and post-conditions
  void PreResolveTopLevelDecl(TopLevelDeclWithMembers cl) {
    var invariantMember = (Invariant)cl.Members.Find(member => member is Invariant);

    if (invariantMember is null) {
      // No invariant, nothing to be done
      return;
    }

    Expression S(string s) {
      return Expression.CreateStringLiteral(Token.NoToken, s);
    }
    
    // We use the underlying invariant clauses instead of the predicate body
    // For proper error localization
    var clauses = invariantMember.Clauses;
    foreach (var clause in clauses) {
      if (!Attributes.Contains(clause.Attributes, "error")) {
        clause.Attributes = new Attributes("error",
          [S("this invariant could not be proved"), S("this invariant holds")], clause.Attributes);
      }
    }
    
    foreach (var member in cl.Members) {
      switch (member) {
        case Constructor ctor: // Constructors have the invariant as additional ensures clauses
          ctor.Ens.AddRange(clauses); // See below why invariant clauses are added last
          break;
        case Method method: // Currently, we assume that each method is public and, as such, needs to require/ensure the invariant
          // Have to add the invariant at the front of the requires clauses, in case subsequent clauses depend on them to be well-formed
          method.Req.InsertRange(0, clauses);
          method.Ens.AddRange(clauses); // Dually, the invariant is ensured last
          break;
        case Invariant:
          break; // Nothing to do for invariants
        case Function function: // Functions need only assume the invariant TODO: also hits functions that should be exempt
          //xfunction.Req.InsertRange(0, clauses);
          break;
      }
    }
  }
}