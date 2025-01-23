using System.Collections.Generic;

namespace Microsoft.Dafny;

public class SpecialFunction(
  IOrigin rangeOrigin,
  string name,
  ModuleDefinition module,
  bool hasStaticKeyword,
  bool isGhost,
  List<TypeParameter> typeArgs,
  List<Formal> ins,
  Type resultType,
  List<AttributedExpression> req,
  Specification<FrameExpression> reads,
  List<AttributedExpression> ens,
  Specification<Expression> decreases,
  Expression body,
  Attributes attributes,
  IOrigin signatureEllipsis)
  : Function(rangeOrigin, new Name(name), hasStaticKeyword, isGhost, false, typeArgs, ins, null, resultType, req, reads,
    ens, decreases, body, null, null, attributes, signatureEllipsis), ICallable {
  ModuleDefinition IASTVisitorContext.EnclosingModule { get { return module; } }
  string ICallable.NameRelativeToModule { get { return Name; } }
}