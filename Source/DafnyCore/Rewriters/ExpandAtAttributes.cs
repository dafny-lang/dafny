using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// Expands @Attribute to their previous version {:attribute} when recognized
/// Marks recognized user-supplied @-attributes as .Builtin = true
/// That way, only those not .Builtin are resolved.
/// </summary>
public class ExpandAtAttributes : IRewriter {
  private readonly SystemModuleManager systemModuleManager;
  public ExpandAtAttributes(Program program, ErrorReporter reporter)
    : base(reporter) {
    Contract.Requires(reporter != null);
    Contract.Requires(systemModuleManager != null);
    systemModuleManager = program.SystemModuleManager;
  }

  internal override void PreResolve(Program program) {
    program.Visit((INode node) => {
      if (node is not IAttributeBearingDeclaration attributeHost) {
        return true;
      }

      Attributes extraAttrs = null;
      foreach (var attr in attributeHost.Attributes.AsEnumerable()) {
        if (attr is not UserSuppliedAtAttribute userSuppliedAtAttribute) {
          continue;
        }

        var newAttributes = Attributes.ExpandAtAttribute(program, userSuppliedAtAttribute, attributeHost);
        Attributes.MergeInto(ref newAttributes, ref extraAttrs);
      }

      var newAttrs = attributeHost.Attributes;
      Attributes.MergeInto(ref extraAttrs, ref newAttrs);
      attributeHost.Attributes = newAttrs;

      return true;
    });
  }
}