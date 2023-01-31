using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// Subclass of Cloner that collects some common functionality between ExtremeLemmaSpecificationSubstituter and
/// ExtremeLemmaBodyCloner.
/// </summary>
abstract class ExtremeCloner : Cloner {
  protected readonly Expression k;
  protected readonly ErrorReporter reporter;
  protected readonly string suffix;
  protected ExtremeCloner(Expression k, ErrorReporter reporter) {
    Contract.Requires(k != null);
    Contract.Requires(reporter != null);
    this.k = k;
    this.reporter = reporter;
    this.suffix = string.Format("#[{0}]", Printer.ExprToString(k));
  }
  protected Expression CloneCallAndAddK(ApplySuffix e) {
    Contract.Requires(e != null);
    Contract.Requires(e.Resolved is FunctionCallExpr && ((FunctionCallExpr)e.Resolved).Function is ExtremePredicate);
    Contract.Requires(e.Lhs is NameSegment || e.Lhs is ExprDotName);
    if (this.CloneResolvedFields) {
      throw new NotImplementedException();
    }

    Expression lhs;
    string name;
    if (e.Lhs is NameSegment ns) {
      name = ns.Name;
      lhs = new NameSegment(Tok(ns.RangeToken), name + "#", ns.OptTypeArguments?.ConvertAll(CloneType));
    } else {
      var edn = (ExprDotName)e.Lhs;
      name = edn.SuffixName;
      lhs = new ExprDotName(Tok(edn.RangeToken), CloneExpr(edn.Lhs), name + "#", edn.OptTypeArguments?.ConvertAll(CloneType));
    }
    var args = new List<ActualBinding>();
    args.Add(new ActualBinding(null, k));
    foreach (var arg in e.Bindings.ArgumentBindings) {
      args.Add(CloneActualBinding(arg));
    }
    var apply = new ApplySuffix(Tok(e.RangeToken), e.AtTok == null ? null : Tok(e.AtTok), lhs, args, Tok(e.CloseParen));
    reporter.Info(MessageSource.Cloner, e.tok, name + suffix);
    return apply;
  }

  protected Expression CloneCallAndAddK(FunctionCallExpr e) {
    Contract.Requires(e != null);
    Contract.Requires(e.Function is ExtremePredicate);
    if (CloneResolvedFields) {
      throw new NotImplementedException();
    }
    var receiver = CloneExpr(e.Receiver);
    var args = new List<ActualBinding>();
    args.Add(new ActualBinding(null, k));
    foreach (var binding in e.Bindings.ArgumentBindings) {
      args.Add(CloneActualBinding(binding));
    }
    var fexp = new FunctionCallExpr(Tok(e.RangeToken), e.NameNode.Append("#"), receiver, args, e.AtLabel);
    reporter.Info(MessageSource.Cloner, e.tok, e.Name + suffix);
    return fexp;
  }
}
