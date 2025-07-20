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
    // Search for inherited invariants too! We must please the override checker
    var invariantMember = cl.Invariant;

    if (invariantMember is null) {
      // No invariant, nothing to be done
      return;
    }

    Expression S(string s) {
      return Expression.CreateStringLiteral(Token.NoToken, s);
    }
    
    // We use the underlying invariant clauses instead of the predicate body
    // For proper error localization
    // TODO(somayyas): kind of a gross and inconsistent way of preserving attributes,
    // we should probably just call the invariant directly
    
    var clauses = invariantMember.Clauses;
    foreach (var clause in clauses) {
      if (!Attributes.Contains(clause.Attributes, "error")) {
        clause.Attributes = new Attributes("error",
          [S("this invariant could not be proved"), S("this invariant holds")], clause.Attributes);
      }
    }
    
    // Note: the following transformations approximate assuming/asserting the invariant for every object in the open set
    // when it is just {this}. Once we have openness annotations, this will have to be generalized.
    foreach (var member in cl.Members) {
      switch (member) {
        case Constructor ctor: // Constructors have the invariant as additional ensures clauses
          ctor.Ens.InsertRange(0, clauses);
          break;
        case Method { IsStatic: false } method: // Currently, we assume that each (instance) method is public and, as such, needs to require/ensure the invariant
          // Have to add the invariant at the front of the requires clauses, in case subsequent clauses depend on them to be well-formed
          method.Req.InsertRange(0, clauses);
          method.Ens.InsertRange(0, clauses); // Postcondition may depend on invariant for well-formedness
          break;
        case Invariant:
          break; // Nothing to do for invariants (have to catch it before Function)
        case Function function: // Functions need only assume the invariant
          function.Req.InsertRange(0, clauses);
          break;
      }
    }
  }
}