using System.Collections.Generic;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

public class ReadFrameSubset : ProofObligationDescription {
  public override DafnyDiagnostic GetDiagnostic(TokenRange range) {
    var (formatMsg, arguments) = GetDeets();
    return new DafnyDiagnostic(MessageSource.Verifier, "", range, formatMsg, arguments.ToArray(), ErrorLevel.Error, []);
  }

  (string FormatMsg, List<object> Arguments) GetDeets() {
    var arguments = new List<object>() { whatKind };
    var message = "insufficient reads clause to {0}";
    if (readExpression is null) {
      return (message, arguments);
    }
    if (scope is { Designator: var designator }) {
      var lambdaScope = scope as LambdaExpr;
      var extraHint = "";
      var obj = "object";
      if (readExpression is MemberSelectExpr e) {
        obj = Printer.ExprToString(DafnyOptions.DefaultImmutableOptions, e.Obj, new PrintFlags(UseOriginalDafnyNames: true));
      } else if (readExpression is SeqSelectExpr s) {
        obj = Printer.ExprToString(DafnyOptions.DefaultImmutableOptions, s.Seq, new PrintFlags(UseOriginalDafnyNames: true));
      } else if (readExpression is MultiSelectExpr m) {
        obj = Printer.ExprToString(DafnyOptions.DefaultImmutableOptions, m.Array,
          new PrintFlags(UseOriginalDafnyNames: true));
      }

      if (scope is Function { CoClusterTarget: var x } && x != Function.CoCallClusterInvolvement.None) {
      } else {
        arguments.Add(obj);
        arguments.Add(designator);
        arguments.Add(readExpression.ToString());
        if (lambdaScope == null && readExpression is MemberSelectExpr { MemberName: var field }) {
          arguments.Add(field);
          extraHint = " or 'reads {1}`{4}'";
        }
        var hint = "adding 'reads {1}'" + extraHint + " in the enclosing {2} specification for resolution";
        if (lambdaScope != null && lambdaScope.Reads.Expressions!.Count == 0) {
          hint = "extracting {3} to a local variable before the lambda expression, or {hint}";
        }

        return (message + $"; Consider {hint}", arguments);
      }
    }

    string whyNotWhat = "Memory locations";

    if (whatKind == "read field") {
      whyNotWhat = "Mutable fields";
    } else if (whatKind is "read array element" or "read the indicated range of array elements") {
      whyNotWhat = "Array elements";
    }

    arguments.Add(whyNotWhat);
    return (message + "; {1} cannot be accessed within certain scopes, such as default values, the right-hand side of constants, or co-recursive calls", arguments);
  }

  public override string SuccessDescription =>
    $"sufficient reads clause to {whatKind}";

  public override string FailureDescription => GetDiagnostic(null).Message;

  public override string ShortDescription => "read frame subset";

  private readonly string whatKind;
  private readonly Expression assertedExpr;
  private readonly Expression readExpression;
  [CanBeNull] private readonly IFrameScope scope;

  public ReadFrameSubset(string whatKind, FrameExpression subsetFrame, List<FrameExpression> supersetFrames, Expression readExpression = null, [CanBeNull] IFrameScope scope = null)
    : this(whatKind, [subsetFrame], supersetFrames, readExpression, scope) { }

  public ReadFrameSubset(string whatKind, List<FrameExpression> subsetFrames, List<FrameExpression> supersetFrames, Expression readExpression = null, [CanBeNull] IFrameScope scope = null)
    : this(whatKind, Utils.MakeDafnyMultiFrameCheck(supersetFrames, subsetFrames), readExpression, scope) { }

  public ReadFrameSubset(string whatKind, Expression assertedExpr, Expression readExpression = null, [CanBeNull] IFrameScope scope = null) {
    this.whatKind = whatKind;
    this.assertedExpr = assertedExpr;
    this.readExpression = readExpression;
    this.scope = scope;
  }

  public override Expression GetAssertedExpr(DafnyOptions options) {
    return assertedExpr;
  }
}