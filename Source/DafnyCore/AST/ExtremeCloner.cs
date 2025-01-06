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
    this.suffix = $"#[{Printer.ExprToString(reporter.Options, k)}]";
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
      lhs = new NameSegment(Origin(ns.Origin), name + "#", ns.OptTypeArguments?.ConvertAll(CloneType));
    } else {
      var edn = (ExprDotName)e.Lhs;
      name = edn.SuffixName;
      lhs = new ExprDotName(Origin(edn.Origin), CloneExpr(edn.Lhs), new Name(name + "#"), edn.OptTypeArguments?.ConvertAll(CloneType));
    }
    var args = new List<ActualBinding>();
    args.Add(new ActualBinding(null, k));
    foreach (var arg in e.Bindings.ArgumentBindings) {
      args.Add(CloneActualBinding(arg));
    }
    var apply = new ApplySuffix(Origin(e.Origin), e.AtTok == null ? null : Origin(e.AtTok), lhs, args, e.CloseParen);
    reporter.Info(MessageSource.Cloner, e.Origin, name + suffix);
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
    var fexp = new FunctionCallExpr(Origin(e.Origin), e.NameNode.Append("#"), receiver, e.OpenParen, e.CloseParen, args, e.AtLabel);
    reporter.Info(MessageSource.Cloner, e.Origin, e.Name + suffix);
    return fexp;
  }

  protected Expression CloneEqualityAndAddK(BinaryExpr binaryExpr) {
    if (this.CloneResolvedFields) {
      throw new NotImplementedException();
    }

    var eq = new TernaryExpr(Origin(binaryExpr.Origin),
      binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon ? TernaryExpr.Opcode.PrefixEqOp : TernaryExpr.Opcode.PrefixNeqOp,
      k, CloneExpr(binaryExpr.E0), CloneExpr(binaryExpr.E1));
    reporter.Info(MessageSource.Cloner, binaryExpr.Origin, "==" + suffix);
    return eq;
  }
}
