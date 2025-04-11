#nullable enable

using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class DatatypeValue : Expression, IHasReferences, ICloneable<DatatypeValue>, ICanFormat {
  public string DatatypeName;
  public string MemberName;
  public ActualBindings Bindings;
  public List<Expression> Arguments => Bindings.Arguments;

  public override IEnumerable<INode> Children => new Node[] { Bindings };

  [FilledInDuringResolution] public DatatypeCtor? Ctor;
  [FilledInDuringResolution] public List<Type> InferredTypeArgs = [];
  [FilledInDuringResolution] public List<PreType> InferredPreTypeArgs = [];
  [FilledInDuringResolution] public bool IsCoCall;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Ctor == null || InferredTypeArgs.Count == Ctor?.EnclosingDatatype?.TypeArgs.Count);
  }

  public DatatypeValue Clone(Cloner cloner) {
    return new DatatypeValue(cloner, this);
  }

  public DatatypeValue(Cloner cloner, DatatypeValue original) : base(cloner, original) {
    DatatypeName = original.DatatypeName;
    MemberName = original.MemberName;
    Bindings = new ActualBindings(cloner, original.Bindings);

    if (cloner.CloneResolvedFields) {
      Ctor = original.Ctor;
      IsCoCall = original.IsCoCall;
      InferredTypeArgs = original.InferredTypeArgs;
    }
  }

  public DatatypeValue(IOrigin origin, string datatypeName, string memberName, [Captured] List<ActualBinding> arguments)
    : this(origin, datatypeName, memberName, new ActualBindings(arguments)) {
  }

  [SyntaxConstructor]
  public DatatypeValue(IOrigin origin, string datatypeName, string memberName, ActualBindings bindings)
    : base(origin) {
    DatatypeName = datatypeName;
    MemberName = memberName;
    Bindings = bindings;
  }

  /// <summary>
  /// This constructor is intended to be used when constructing a resolved DatatypeValue. The "args" are expected
  /// to be already resolved, and are all given positionally.
  /// </summary>
  public DatatypeValue(IOrigin origin, string datatypeName, string memberName, List<Expression> arguments)
    : this(origin, datatypeName, memberName, arguments.ConvertAll(e => new ActualBinding(null, e))) {
    Bindings.AcceptArgumentExpressionsAsExactParameterList();
  }

  public override IEnumerable<Expression> SubExpressions =>
    Arguments ?? Enumerable.Empty<Expression>();

  public IEnumerable<Reference> GetReferences() {
    return Enumerable.Repeat(new Reference(ReportingRange, Ctor), 1);
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    formatter.SetMethodLikeIndent(StartToken, OwnedTokens, indentBefore);
    return true;
  }
}