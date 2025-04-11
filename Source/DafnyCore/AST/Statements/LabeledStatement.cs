#nullable enable
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class LabeledStatement : Statement, ICloneable<LabeledStatement> {
  public List<Label> Labels { get; set; }

  public LabeledStatement(Cloner cloner, LabeledStatement original) : base(cloner, original) {
    Labels = original.Labels.Where(l => l.Name != null || cloner.CloneResolvedFields).
      Select(l => new Label(cloner.Origin(l.Tok), l.Name)).ToList();
  }

  [SyntaxConstructor]
  public LabeledStatement(IOrigin origin, List<Label> labels, Attributes? attributes = null) : base(origin, attributes) {
    Labels = labels;
  }

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable, ICodeContext codeContext,
    string? proofContext, bool allowAssumptionVariables, bool inConstructorInitializationPhase) {
    IsGhost = true;
  }

  public LabeledStatement Clone(Cloner cloner) {
    return new LabeledStatement(cloner, this);
  }
}