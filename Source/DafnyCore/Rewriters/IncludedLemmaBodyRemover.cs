using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// Lemma's from included files do not need to be resolved and translated
/// so we return emptyBody. This is to speed up resolver and translator.
/// </summary>
public class IncludedLemmaBodyRemover : IRewriter {
  private readonly Program program;

  public IncludedLemmaBodyRemover(Program program, ErrorReporter reporter)
    : base(reporter) {
    this.program = program;
  }

  private static readonly BlockStmt EmptyBody = new(Token.NoToken.ToRange(), new List<Statement>());

  internal override void PostResolve(ModuleDefinition moduleDefinition) {
    // TODO
    // var moduleFile = moduleDefinition.Tok.Uri;
    // if (moduleFile == null) {
    //   return; // The default module doesn't refine any modules
    // }
    foreach (var method in moduleDefinition.TopLevelDecls.OfType<TopLevelDeclWithMembers>().
               SelectMany(withMembers => withMembers.Members.OfType<Method>())) {
      if (method.Body != null && method.IsLemmaLike && method.Tok.IsIncludeToken(program)) {
        method.Body = EmptyBody;
      }
    }
  }
}

// Different files that are all using the default module