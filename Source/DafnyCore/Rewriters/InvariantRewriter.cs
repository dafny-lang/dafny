using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class InvariantRewriter(Program program, ErrorReporter reporter) : IRewriter(reporter) {
  internal override void PostResolve(ModuleDefinition module) {
    foreach (var decl in module.TopLevelDecls) {
      if (decl is TopLevelDeclWithMembers cl) {
        PostResolveTopLevelDecl(cl);
      }
    }
  }
  
  // Add invariants as pre- and post-conditions
  void PostResolveTopLevelDecl(TopLevelDeclWithMembers cl) {
    var invariantMember = (Invariant)cl.Members.Find(member => member is Invariant);

    if (invariantMember is null) {
      // No invariant, nothing to be done
      return;
    }

    var thisExpr = new ThisExpr(cl);

    Expression S(string s) {
      return Expression.CreateStringLiteral(Token.NoToken, s);
    }
    
    foreach (var member in cl.Members) {
      // TODO(somayyas): can we give better error messages here?
      AttributedExpression invariant =
        new(invariantMember.ResolvedCall(Token.NoToken, thisExpr, program.SystemModuleManager),
          new Attributes("error", [S("this invariant could not be proved"), S("this invariant holds")], null));
      switch (member) {
        case Constructor ctor: // Constructors have the invariant as additional ensures clauses
          ctor.Ens.Add(invariant); // See below why invariant clauses are added last
          break;
        case Method method: // Currently, we assume that each method is public and, as such, needs to require/ensure the invariant
          // Have to add the invariant at the front of the requires clauses, in case subsequent clauses depend on them to be well-formed
          method.Req.Insert(0, invariant);
          method.Ens.Add(invariant); // Dually, the invariant is ensured last
          break;
        case Invariant: break; // Nothing to do for invariants
        case Function function: // Functions need only assume the invariant
          function.Req.Insert(0, invariant);
          break;
      }
    }
  }
}