using System.Collections.Generic;
using System.Diagnostics.Contracts;
using static Microsoft.Dafny.RewriterErrors;

namespace Microsoft.Dafny;

/// <summary>
/// Replace all occurrences of attribute {:timeLimitMultiplier X} with {:timeLimit Y}
/// where Y = X*default-time-limit or Y = X*command-line-time-limit
/// </summary>
public class TimeLimitRewriter : IRewriter {
  public TimeLimitRewriter(ErrorReporter reporter)
    : base(reporter) {
    Contract.Requires(reporter != null);
  }

  internal override void PreResolve(ModuleDefinition m) {
    foreach (var d in m.TopLevelDecls) {
      if (d is TopLevelDeclWithMembers tld) {
        foreach (MemberDecl member in tld.Members) {
          if (member is Function || member is MethodOrConstructor) {
            // Check for the timeLimitMultiplier attribute
            if (Attributes.Contains(member.Attributes, "timeLimitMultiplier")) {
              Attributes attrs = member.Attributes;
              foreach (var attr in attrs.AsEnumerable()) {
                if (attr.Name == "timeLimitMultiplier") {
                  if (attr.Args.Count == 1 && attr.Args[0] is LiteralExpr) {
                    var arg = attr.Args[0] as LiteralExpr;
                    System.Numerics.BigInteger value = (System.Numerics.BigInteger)arg.Value;
                    if (value.Sign > 0) {
                      uint currentLimit = 0;
                      string name = "";
                      if (Reporter.Options.ResourceLimit > 0) {
                        // Interpret this as multiplying the resource limit
                        currentLimit = Reporter.Options.ResourceLimit;
                        name = "rlimit";
                      } else {
                        // Interpret this as multiplying the time limit
                        currentLimit = Reporter.Options.TimeLimit > 0 ? Reporter.Options.TimeLimit : 10;  // Default to 10 seconds
                        name = "timeLimit";
                      }
                      Expression newArg = new LiteralExpr(attr.Args[0].Origin, value * currentLimit);
                      member.Attributes = new Attributes("_" + name, [newArg], attrs);
                      if (Attributes.Contains(attrs, name)) {
                        ReportWarning(ErrorId.rw_timelimit_multiplier, member.Origin, "timeLimitMultiplier annotation overrides " + name + " annotation");
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