using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// Lemma from included files do not need to be resolved and translated
/// so we return emptyBody. This is to speed up resolver and translator.
/// </summary>
public class IncludedLemmaBodyRemover : IRewriter {
  public IncludedLemmaBodyRemover(ErrorReporter reporter)
    : base(reporter) {
  }

  private static readonly BlockStmt EmptyBody = new(Token.NoToken.ToRange(), new List<Statement>());

  internal override void PostResolve(ModuleDefinition moduleDefinition) {
    foreach (var method in moduleDefinition.TopLevelDecls.OfType<TopLevelDeclWithMembers>().
               SelectMany(withMembers => withMembers.Members.OfType<Method>())) {
      if (method.Body != null && method.IsLemmaLike && method.Tok is IncludeToken && !DafnyOptions.O.VerifyAllModules) {
        method.Body = EmptyBody;
      }
    }
  }
}