using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// Replace all occurrences of attribute {:timeLimitMultiplier X} with {:timeLimit Y}
/// where Y = X*default-time-limit or Y = X*command-line-time-limit
/// </summary>
public class TimeLimitRewriter : IRewriter {
  private DafnyOptions options;
  public TimeLimitRewriter(ErrorReporter reporter, DafnyOptions options)
    : base(reporter) {
    Contract.Requires(reporter != null);
    this.options = options;
  }

  internal override void PreResolve(ModuleDefinition m) {
    foreach (var d in m.TopLevelDecls) {
      if (d is TopLevelDeclWithMembers tld) {
        foreach (MemberDecl member in tld.Members) {
          if (member is Function || member is Method) {
            // Check for the timeLimitMultiplier attribute
            if (Attributes.Contains(member.Attributes, "timeLimitMultiplier")) {
              Attributes attrs = member.Attributes;
              foreach (var attr in attrs.AsEnumerable()) {
                if (attr.Name == "timeLimitMultiplier") {
                  if (attr.Args.Count == 1 && attr.Args[0] is LiteralExpr) {
                    var arg = attr.Args[0] as LiteralExpr;
                    System.Numerics.BigInteger value = (System.Numerics.BigInteger)arg.Value;
                    if (value.Sign > 0) {
                      uint current_limit = 0;
                      string name = "";
                      if (options.ResourceLimit > 0) {
                        // Interpret this as multiplying the resource limit
                        current_limit = options.ResourceLimit;
                        name = "rlimit";
                      } else {
                        // Interpret this as multiplying the time limit
                        current_limit = options.TimeLimit > 0 ? options.TimeLimit : 10;  // Default to 10 seconds
                        name = "timeLimit";
                      }
                      Expression newArg = new LiteralExpr(attr.Args[0].tok, value * current_limit);
                      member.Attributes = new Attributes("_" + name, new List<Expression>() { newArg }, attrs);
                      if (Attributes.Contains(attrs, name)) {
                        Reporter.Warning(MessageSource.Rewriter, ErrorDetail.ErrorID.None, member.tok, "timeLimitMultiplier annotation overrides " + name + " annotation");
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}