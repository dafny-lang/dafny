using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny.LanguageServer.CounterExampleGeneration;

public abstract class Constraint {
  private readonly List<PartialValue> referencedValues;
  public IEnumerable<PartialValue> ReferencedValues => referencedValues.AsEnumerable();

  protected Constraint(IEnumerable<PartialValue> referencedValues) {
    this.referencedValues = referencedValues.ToList();
    foreach (var partialValue in this.referencedValues) {
      partialValue.Constraints.Add(this);
    }
  }

  public Expression? AsExpression(Dictionary<PartialValue, Expression> definitions, bool wrapDefinitions) {
    if (referencedValues.Any(value => !definitions.ContainsKey(value))) {
      return null;
    }
    var expression = AsExpression(definitions);
    if (this is not DefinitionConstraint definitionConstraint) {
      expression.Type = Type.Bool;
      return expression;
    }
    expression.Type = definitionConstraint.DefinedValue.Type;
    if (!wrapDefinitions) {
      return expression;
    }

    if (!definitions.ContainsKey(definitionConstraint.DefinedValue)) {
      return null;
    }
    return definitionConstraint.WrapDefinition(definitions, expression);
  }

  public override string ToString() {
    var temporaryIds = new Dictionary<PartialValue, Expression>();
    foreach (var partialValue in referencedValues) {
      temporaryIds[partialValue] = new IdentifierExpr(Token.NoToken, "E#" + partialValue.Element.Id);
    }
    return AsExpression(temporaryIds, false)?.ToString() ?? "";
  }

  protected abstract Expression AsExpression(Dictionary<PartialValue, Expression> definitions);


  public static void FindDefinitions(Dictionary<PartialValue, Expression> knownDefinitions, List<Constraint> constraints, bool allowNewIdentifiers) {
    Constraint? newConstraint = null;
    var oldConstraints = new List<Constraint>();
    oldConstraints.AddRange(constraints.Where(constraint => allowNewIdentifiers || constraint is not IdentifierExprConstraint));
    constraints.Clear();
    do {
      if (newConstraint != null) {
        oldConstraints.Remove(newConstraint);
      }

      var litConstraint = oldConstraints.OfType<LiteralExprConstraint>()
        .FirstOrDefault(definition => !knownDefinitions.ContainsKey(definition.DefinedValue));
      if (litConstraint != null) {
        knownDefinitions[litConstraint.DefinedValue] = litConstraint.AsExpression(knownDefinitions, false);
        newConstraint = litConstraint;
        continue;
      }

      newConstraint = oldConstraints.FirstOrDefault(constraint =>
        constraint is not DefinitionConstraint &&
        constraint.ReferencedValues.All(knownDefinitions.ContainsKey));
      if (newConstraint != null) {
        constraints.Add(newConstraint);
        continue;
      }

      var definition = oldConstraints.OfType<DefinitionConstraint>().FirstOrDefault(definition =>
        !knownDefinitions.ContainsKey(definition.DefinedValue) &&
        definition.ReferencedValues.All(knownDefinitions.ContainsKey));
      if (definition != null) {
        constraints.AddRange(definition.WellFormed);
        knownDefinitions[definition.DefinedValue] = definition.AsExpression(knownDefinitions, false);
        newConstraint = definition;
        continue;
      }

      newConstraint = oldConstraints.FirstOrDefault();
      if (newConstraint != null) {
        if (newConstraint is DefinitionConstraint definitionConstraint) {
          constraints.AddRange(definitionConstraint.WellFormed);
        }
        constraints.Add(newConstraint);
      }
    } while (newConstraint != null);
  }

}

public abstract class DefinitionConstraint : Constraint {

  public readonly PartialValue DefinedValue;
  public readonly List<Constraint> WellFormed;

  protected DefinitionConstraint(IEnumerable<PartialValue> referencedValues, PartialValue definedValue, List<Constraint> wellFormed) : base(referencedValues) {
    DefinedValue = definedValue;
    DefinedValue.Constraints.Add(this);
    WellFormed = wellFormed;
  }

  internal Expression WrapDefinition(Dictionary<PartialValue, Expression> definitions, Expression expression) {
    var binaryExpr = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, definitions[DefinedValue], expression) {
      Type = Type.Bool
    };
    return binaryExpr;
  }
}

public class IdentifierExprConstraint : DefinitionConstraint {
  private readonly string name;

  public IdentifierExprConstraint(PartialValue definedValue, string name) : base(new List<PartialValue>(), definedValue, new List<Constraint>() { }) {
    this.name = name;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new IdentifierExpr(Token.NoToken, name);
  }
}

public class LiteralExprConstraint : DefinitionConstraint {

  public readonly Expression LiteralExpr;
  public LiteralExprConstraint(PartialValue definedValue, Expression literalExpr) : base(new List<PartialValue>(), definedValue, new List<Constraint>() { }) {
    LiteralExpr = literalExpr;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return LiteralExpr;
  }
}

public abstract class MemberSelectExprConstraint : DefinitionConstraint {

  public readonly PartialValue Obj;
  public readonly string MemberName;

  protected MemberSelectExprConstraint(PartialValue definedValue, PartialValue obj, string memberName, List<Constraint> constraint) : base(new List<PartialValue> { obj }, definedValue, constraint) {
    Obj = obj;
    MemberName = memberName;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new MemberSelectExpr(Token.NoToken, definitions[Obj], MemberName);
  }
}

public class MemberSelectExprDatatypeConstraint : MemberSelectExprConstraint {
  public MemberSelectExprDatatypeConstraint(PartialValue definedValue, PartialValue obj, string memberName) : base(
    definedValue, obj, memberName, new List<Constraint>() { }) {
  }
}

public class MemberSelectExprClassConstraint : MemberSelectExprConstraint {
  public MemberSelectExprClassConstraint(PartialValue definedValue, PartialValue obj, string memberName) : base(
    definedValue, obj, memberName, new List<Constraint>() { new NotNullConstraint(obj) }) {
  }
}

public class DatatypeValueConstraint : DefinitionConstraint {

  public readonly IEnumerable<PartialValue> UnnamedDestructors;
  private readonly string constructorName;
  private readonly string datatypeName;

  public DatatypeValueConstraint(PartialValue definedValue, string datatypeName, string constructorName, IReadOnlyCollection<PartialValue> unnamedDestructors) : base(unnamedDestructors, definedValue, new List<Constraint>() { }) {
    UnnamedDestructors = unnamedDestructors;
    this.constructorName = constructorName;
    this.datatypeName = datatypeName;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new DatatypeValue(Token.NoToken, datatypeName,
      constructorName,
      UnnamedDestructors.Select(destructor => definitions[destructor]).ToList());
  }
}

public class SeqSelectExprConstraint : DefinitionConstraint {

  public readonly PartialValue Seq;
  public readonly PartialValue Index;


  public SeqSelectExprConstraint(PartialValue definedValue, PartialValue seq, PartialValue index) : base(new List<PartialValue> { seq, index }, definedValue, new List<Constraint>() { new CardinalityGtThanConstraint(seq, index) }) {
    Seq = seq;
    Index = index;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new SeqSelectExpr(Token.NoToken, true, definitions[Seq], definitions[Index], null, Token.NoToken);
  }
}

public class SeqSelectExprArrayConstraint : DefinitionConstraint {
  private readonly PartialValue array;
  private readonly string index;


  // TODO: Add well-formed-ness constraint for array indexing!
  public SeqSelectExprArrayConstraint(PartialValue definedValue, PartialValue array, string index) : base(new List<PartialValue> { array }, definedValue, new List<Constraint>() { }) {
    this.array = array;
    this.index = index;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new SeqSelectExpr(Token.NoToken, true, definitions[array], new NameSegment(Token.NoToken, index, null), null, Token.NoToken);
  }
}

public class MapSelectExprConstraint : DefinitionConstraint {

  public readonly PartialValue Map;
  public readonly PartialValue Key;


  public MapSelectExprConstraint(PartialValue definedValue, PartialValue map, PartialValue key) : base(
    new List<PartialValue> { map, key }, definedValue, new List<Constraint>() { new ContainmentConstraint(key, map, true) }) {
    Map = map;
    Key = key;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new SeqSelectExpr(Token.NoToken, true, definitions[Map], definitions[Key], null, Token.NoToken);
  }
}

public class SeqSelectExprWithLiteralConstraint : DefinitionConstraint {

  public readonly PartialValue Seq;
  public readonly LiteralExpr Index;


  public SeqSelectExprWithLiteralConstraint(PartialValue definedValue, PartialValue seq, LiteralExpr index) : base(
    new List<PartialValue> { seq }, definedValue, new List<Constraint>() { new CardinalityGtThanLiteralConstraint(seq, index) }) {
    Seq = seq;
    Index = index;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new SeqSelectExpr(Token.NoToken, true, definitions[Seq], Index, null, Token.NoToken);
  }
}

public class CardinalityConstraint : DefinitionConstraint {

  public readonly PartialValue Collection;


  public CardinalityConstraint(PartialValue definedValue, PartialValue collection) : base(new List<PartialValue> { collection }, definedValue, new List<Constraint>() { }) {
    Collection = collection;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new UnaryOpExpr(Token.NoToken, UnaryOpExpr.Opcode.Cardinality, definitions[Collection]);
  }
}

public class SeqDisplayConstraint : DefinitionConstraint {
  private readonly List<PartialValue> elements;


  public SeqDisplayConstraint(PartialValue definedValue, List<PartialValue> elements) : base(elements, definedValue, new List<Constraint>() { }) {
    this.elements = elements;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new SeqDisplayExpr(Token.NoToken, elements.ConvertAll(element => definitions[element]));
  }
}

public class FunctionCallConstraint : DefinitionConstraint {
  private readonly List<PartialValue> args;
  private readonly PartialValue receiver;
  public readonly string functionName;


  public FunctionCallConstraint(
    PartialValue definedValue,
    PartialValue receiver,
    List<PartialValue> args,
    string functionName,
    bool receiverIsReferenceType) : base(args.Append(receiver), definedValue,
    receiverIsReferenceType ? new List<Constraint> { new NotNullConstraint(receiver), new FunctionCallRequiresConstraint(receiver, args, functionName) } : new List<Constraint>() { new FunctionCallRequiresConstraint(receiver, args, functionName) }) {
    this.args = args;
    this.receiver = receiver;
    this.functionName = functionName;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new ApplySuffix(
      Token.NoToken,
      null,
      new ExprDotName(Token.NoToken, definitions[receiver], functionName, null),
      args.Select(formal =>
        new ActualBinding(null, definitions[formal])).ToList(),
      Token.NoToken);
  }
}

public class FunctionCallRequiresConstraint : Constraint {
  private readonly List<PartialValue> args;
  private readonly PartialValue receiver;
  public readonly string functionName;


  public FunctionCallRequiresConstraint(PartialValue receiver, List<PartialValue> args, string functionName) : base(args.Append(receiver)) {
    this.args = args;
    this.receiver = receiver;
    this.functionName = functionName;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new ApplySuffix(
      Token.NoToken,
      null,
      new ExprDotName(Token.NoToken, definitions[receiver], functionName + ".requires", null),
      args.Select(formal =>
        new ActualBinding(null, definitions[formal])).ToList(),
      Token.NoToken);
  }
}

public class ContainmentConstraint : Constraint {

  public readonly PartialValue Element, Set;
  private readonly bool isIn;
  public ContainmentConstraint(PartialValue element, PartialValue set, bool isIn) : base(new List<PartialValue> { element, set }) {
    Element = element;
    Set = set;
    this.isIn = isIn;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new BinaryExpr(
      Token.NoToken,
      isIn ? BinaryExpr.Opcode.In : BinaryExpr.Opcode.NotIn,
      definitions[Element],
      definitions[Set]);
  }
}

public class NeqConstraint : Constraint {
  private readonly PartialValue value;
  private readonly PartialValue neq;
  public NeqConstraint(PartialValue value, PartialValue neq) : base(new List<PartialValue> { value, neq }) {
    this.value = value;
    this.neq = neq;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new BinaryExpr(
      Token.NoToken,
      BinaryExpr.Opcode.Neq,
      definitions[value],
      definitions[neq]);
  }
}


public class DatatypeConstructorCheckConstraint : Constraint {
  private readonly PartialValue obj;
  public readonly string ConstructorName;

  public DatatypeConstructorCheckConstraint(PartialValue obj, string constructorName) : base(new List<PartialValue> { obj }) {
    this.obj = obj;
    ConstructorName = constructorName;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new MemberSelectExpr(Token.NoToken, definitions[obj], ConstructorName + "?");
  }
}

public class CardinalityGtThanConstraint : Constraint {
  private readonly PartialValue collection;
  private readonly PartialValue bound;

  public CardinalityGtThanConstraint(PartialValue collection, PartialValue bound) : base(new List<PartialValue> { collection, bound }) {
    this.collection = collection;
    this.bound = bound;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    var cardinalityExpr = new UnaryOpExpr(Token.NoToken, UnaryOpExpr.Opcode.Cardinality, definitions[collection]) {
      Type = Type.Int
    };
    return new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Gt, cardinalityExpr, definitions[bound]);
  }
}

public class CardinalityGtThanLiteralConstraint : Constraint {
  private readonly PartialValue collection;
  private readonly LiteralExpr bound;

  public CardinalityGtThanLiteralConstraint(PartialValue collection, LiteralExpr bound) : base(new List<PartialValue> { collection }) {
    this.collection = collection;
    this.bound = bound;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    var cardinalityExpr = new UnaryOpExpr(Token.NoToken, UnaryOpExpr.Opcode.Cardinality, definitions[collection]) {
      Type = Type.Int
    };
    return new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Gt, cardinalityExpr, bound);
  }
}

public class TypeTestConstraint : Constraint {
  private readonly Type type;
  private readonly PartialValue value;
  public TypeTestConstraint(PartialValue value, Type type) : base(new List<PartialValue> { value }) {
    this.type = type;
    this.value = value;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new TypeTestExpr(Token.NoToken, definitions[value], type);
  }
}

public class NotNullConstraint : Constraint {
  private readonly PartialValue value;
  public NotNullConstraint(PartialValue value) : base(new List<PartialValue> { value }) {
    this.value = value;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    var nullValue = new LiteralExpr(Token.NoToken) {
      Type = new InferredTypeProxy()
    };
    return new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Neq, definitions[value], nullValue);
  }
}
