using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using System.Collections.ObjectModel;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny.Triggers { //FIXME rename this file
  internal class QuantifierCollector : TopDownVisitor<object> {
    readonly ErrorReporter reporter;
    internal List<QuantifiersCollection> quantifierCollections = new List<QuantifiersCollection>();

    public QuantifierCollector(ErrorReporter reporter) {
      Contract.Requires(reporter != null);
      this.reporter = reporter;
    }

    protected override bool VisitOneExpr(Expression expr, ref object st) {
      var quantifier = expr as QuantifierExpr;
      if (quantifier != null) {
        if (quantifier.SplitQuantifier != null) {
          var collection = quantifier.SplitQuantifier.Select(q => q as QuantifierExpr).Where(q => q != null);
          quantifierCollections.Add(new QuantifiersCollection(collection, reporter));
          return false;
        } else {
          quantifierCollections.Add(new QuantifiersCollection(Enumerable.Repeat(quantifier, 1), reporter));
        }
      }
      return true;
    }
  }
}
