#nullable enable
using System.Collections.Generic;

namespace Microsoft.Dafny;

public class LabelledStatement : Statement, ICloneable<LabelledStatement> {
  public LList<Label>? Labels { get; set; }
  public LList<Label>? LabelsList =>

  public LabelledStatement(Cloner cloner, LabelledStatement original) : base(cloner, original) {
    var stack = new Stack<Label>();
    for (var head = Labels; head != null; head = head.Next) {
      stack.Push(head.Data);
    }

    foreach (var item in stack) {
      Labels = new LList<Label>(item, Labels);
    }
  }

  public LabelledStatement(IOrigin origin, LList<Label>? labels, Attributes? attributes) : base(origin, attributes) {
    Labels = labels;
  }
  
  public LabelledStatement(IOrigin origin, List<Name> labels, Attributes? attributes) : base(origin, attributes) {
    for (var i = labels.Count; i >= 0; i--) {
      var label = labels[i];
      Labels = new LList<Label>(new Label(label.Origin, label.Value), Labels);
    }
  }
  
  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable, ICodeContext codeContext,
    string? proofContext, bool allowAssumptionVariables, bool inConstructorInitializationPhase) {
  }

  public LabelledStatement Clone(Cloner cloner) {
    return new LabelledStatement(cloner, this);
  }
}