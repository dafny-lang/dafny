// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
#nullable enable

using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

/// <summary>
/// This class represents constraints over partial values in the counterexample model.
/// A constraint is a Boolean expression over partial values.
/// </summary>
public abstract class Constraint {

  // We cannot add a constraint to the counterexample assumption until we know how to refer to each of the
  // partial values referenced by the constraint:
  private readonly List<PartialValue> referencedValues;
  public IEnumerable<PartialValue> ReferencedValues => referencedValues.AsEnumerable();

  protected Constraint(IEnumerable<PartialValue> referencedValues, bool isWellFormedNessConstraint = false) {
    this.referencedValues = referencedValues.ToList();
    if (isWellFormedNessConstraint) {
      return;
    }
    foreach (var partialValue in this.referencedValues) {
      partialValue.Constraints.Add(this);
    }
  }

  /// <summary> Return the Dafny expression corresponding to the constraint. </summary>
  /// <param name="definitions"></param> Maps a partial value to a Dafny expression by which we can refer to this value.
  /// <returns></returns>
  public Expression? AsExpression(Dictionary<PartialValue, Expression> definitions) {
    if (referencedValues.Any(value => !definitions.ContainsKey(value))) {
      return null;
    }
    var expression = AsExpressionHelper(definitions);
    expression.Type = Type.Bool;
    return expression;
  }

  /// <summary> This is intended for debugging as we don't know apriori how to refer to partial values </summary>
  public override string ToString() {
    var temporaryIds = new Dictionary<PartialValue, Expression>();
    foreach (var partialValue in referencedValues) {
      temporaryIds[partialValue] = new IdentifierExpr(Token.NoToken, "E#" + partialValue.Element.Id);
    }
    if (this is DefinitionConstraint definitionConstraint) {
      return definitionConstraint.RightHandSide(temporaryIds).ToString() ?? "";
    }
    return AsExpression(temporaryIds)?.ToString() ?? "";
  }

  protected abstract Expression AsExpressionHelper(Dictionary<PartialValue, Expression> definitions);


  /// <summary>
  /// Take a list of constraints and a dictionary of known ways to refer to partial values.
  /// Update the dictionary according to the constraints in the list and return an ordered list of constraints that
  /// can form a counterexample assumption.
  /// </summary>
  /// <param name="knownDefinitions"></param>
  /// <param name="constraints"></param>
  /// <param name="allowNewIdentifiers"></param> If false, do not allow new referring to partial values by identifiers
  /// <param name="prune"></param> if True, remove constraints over literal values, since those should be self-evident
  /// that are not already in knownDefinitions map
  public static List<Constraint> ResolveAndOrder(
    Dictionary<PartialValue, Expression> knownDefinitions,
    List<Constraint> constraints,
    bool allowNewIdentifiers,
    bool prune) {
    Constraint? newConstraint = null;
    var oldConstraints = new List<Constraint>();
    oldConstraints.AddRange(constraints.Where(constraint =>
      allowNewIdentifiers || constraint is not IdentifierExprConstraint));
    var newConstraints = new List<Constraint>();
    var knownAsLiteral = new HashSet<PartialValue>();
    do {
      if (newConstraint != null) {
        oldConstraints.Remove(newConstraint);
      }

      // Prioritize literals and display expressions
      var displayConstraint = oldConstraints
        .OfType<DefinitionConstraint>()
        .Where(constraint => constraint is LiteralExprConstraint ||
                             constraint is SeqDisplayConstraint ||
                             constraint is DatatypeValueConstraint)
        .FirstOrDefault(constraint => !knownDefinitions.ContainsKey(constraint.DefinedValue)
                                      && constraint.ReferencedValues.All(knownDefinitions.ContainsKey));
      if (displayConstraint != null) {
        knownAsLiteral.Add(displayConstraint.DefinedValue);
        knownDefinitions[displayConstraint.DefinedValue] = displayConstraint.RightHandSide(knownDefinitions);
        knownDefinitions[displayConstraint.DefinedValue].Type = displayConstraint.DefinedValue.Type;
        newConstraint = displayConstraint;
        continue;
      }

      // Add all constrains where we know how to refer to each referenced value
      newConstraint = oldConstraints.Where(constraint =>
        constraint is not DefinitionConstraint &&
        constraint.ReferencedValues.All(knownDefinitions.ContainsKey))
        .FirstOrDefault(constraint => !prune || constraint is IdentifierExprConstraint || constraint.ReferencedValues.Any(value => !knownAsLiteral.Contains(value)));
      if (newConstraint != null) {
        newConstraints.Add(newConstraint);
        continue;
      }

      // update knownDefinitions map with new definitions
      var definition = oldConstraints.OfType<DefinitionConstraint>().FirstOrDefault(definition =>
        !knownDefinitions.ContainsKey(definition.DefinedValue) &&
        definition.ReferencedValues.All(knownDefinitions.ContainsKey));
      if (definition != null) {
        if (!prune || definition is FunctionCallConstraint ||
            definition.referencedValues.Any(value => !knownAsLiteral.Contains(value))) {
          newConstraints.AddRange(definition.WellFormed);
        }
        knownDefinitions[definition.DefinedValue] = definition.RightHandSide(knownDefinitions);
        knownDefinitions[definition.DefinedValue].Type = definition.DefinedValue.Type;
        newConstraint = definition;
        continue;
      }

      // append all other constraints  to the end
      newConstraint = oldConstraints.FirstOrDefault(constraint => !prune || constraint is FunctionCallConstraint || constraint is IdentifierExprConstraint || constraint.referencedValues.Any(value => !knownAsLiteral.Contains(value)));
      if (newConstraint != null) {
        if (newConstraint is DefinitionConstraint definitionConstraint) {
          newConstraints.AddRange(definitionConstraint.WellFormed);
        }

        newConstraints.Add(newConstraint);
      }
    } while (newConstraint != null);

    return newConstraints;
  }

}

/// <summary>
/// Definition Constraint is a constraint that identifies a partial value with an expression over other partial values
/// </summary>
public abstract class DefinitionConstraint : Constraint {

  public readonly PartialValue DefinedValue;
  public readonly List<Constraint> WellFormed;

  protected DefinitionConstraint(
    IEnumerable<PartialValue> referencedValues,
    PartialValue definedValue,
    List<Constraint> wellFormed) : base(referencedValues) {
    DefinedValue = definedValue;
    DefinedValue.Constraints.Add(this);
    WellFormed = wellFormed;
  }

  public abstract Expression RightHandSide(Dictionary<PartialValue, Expression> definitions);

  protected override Expression AsExpressionHelper(Dictionary<PartialValue, Expression> definitions) {
    var expression = RightHandSide(definitions);
    expression.Type = DefinedValue.Type;
    var binaryExpr = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, definitions[DefinedValue], expression) {
      Type = Type.Bool
    };
    return binaryExpr;
  }
}

public class IdentifierExprConstraint : DefinitionConstraint {
  private readonly string name;

  public IdentifierExprConstraint(PartialValue definedValue, string name)
    : base(new List<PartialValue>(), definedValue, new List<Constraint>()) {
    this.name = name;
  }

  public override Expression RightHandSide(Dictionary<PartialValue, Expression> definitions) {
    return new IdentifierExpr(Token.NoToken, name);
  }
}

public class ArraySelectionConstraint : DefinitionConstraint {
  public PartialValue Array;
  public List<LiteralExpr> indices;

  public ArraySelectionConstraint(PartialValue definedValue, PartialValue array, List<LiteralExpr> indices)
    : base(new List<PartialValue>() { array }, definedValue,
      new List<Constraint>() { new ArrayLengthConstraint(array, indices) }) {
    Array = array;
    this.indices = indices;
  }

  public override Expression RightHandSide(Dictionary<PartialValue, Expression> definitions) {
    if (indices.Count == 1) {
      return new SeqSelectExpr(Token.NoToken, true, definitions[Array], indices.First(), null, Token.NoToken);
    }
    return new MultiSelectExpr(Token.NoToken, definitions[Array], indices.OfType<Expression>().ToList());
  }
}

public class LiteralExprConstraint : DefinitionConstraint {

  public readonly Expression LiteralExpr;
  public LiteralExprConstraint(PartialValue definedValue, Expression literalExpr)
    : base(new List<PartialValue>(), definedValue, new List<Constraint>()) {
    LiteralExpr = literalExpr;
  }

  public override Expression RightHandSide(Dictionary<PartialValue, Expression> definitions) {
    return LiteralExpr;
  }
}

public abstract class MemberSelectExprConstraint : DefinitionConstraint {

  public readonly PartialValue Obj;
  public readonly string MemberName;

  protected MemberSelectExprConstraint(
    PartialValue definedValue,
    PartialValue obj,
    string memberName,
    List<Constraint> constraint) : base(new List<PartialValue> { obj }, definedValue, constraint) {
    Obj = obj;
    MemberName = memberName;
  }

  public override Expression RightHandSide(Dictionary<PartialValue, Expression> definitions) {
    return new MemberSelectExpr(Token.NoToken, definitions[Obj], new Name(MemberName));
  }
}

public class MemberSelectExprDatatypeConstraint : MemberSelectExprConstraint {
  public MemberSelectExprDatatypeConstraint(PartialValue definedValue, PartialValue obj, string memberName)
    : base(definedValue, obj, memberName, new List<Constraint>()) { }
}

public class MemberSelectExprClassConstraint : MemberSelectExprConstraint {
  public MemberSelectExprClassConstraint(PartialValue definedValue, PartialValue obj, string memberName)
    : base(definedValue, obj, memberName, new List<Constraint> { new NotNullConstraint(obj) }) {
  }
}

public class DatatypeValueConstraint : DefinitionConstraint {

  public readonly IEnumerable<PartialValue> UnnamedDestructors;
  private readonly string constructorName;
  private readonly string datatypeName;

  public DatatypeValueConstraint(
    PartialValue definedValue,
    string datatypeName,
    string constructorName,
    IReadOnlyCollection<PartialValue> unnamedDestructors)
    : base(unnamedDestructors, definedValue, new List<Constraint>()) {
    UnnamedDestructors = unnamedDestructors;
    this.constructorName = constructorName;
    this.datatypeName = datatypeName;
  }

  public override Expression RightHandSide(Dictionary<PartialValue, Expression> definitions) {
    return new DatatypeValue(Token.NoToken, datatypeName,
      constructorName,
      UnnamedDestructors.Select(destructor => definitions[destructor]).ToList());
  }
}

public class SeqSelectExprConstraint : DefinitionConstraint {

  public readonly PartialValue Seq;
  public readonly PartialValue Index;


  public SeqSelectExprConstraint(PartialValue definedValue, PartialValue seq, PartialValue index) : base(
    new List<PartialValue> { seq, index }, definedValue,
    new List<Constraint> { new CardinalityGtThanConstraint(seq, index) }) {
    Seq = seq;
    Index = index;
  }

  public override Expression RightHandSide(Dictionary<PartialValue, Expression> definitions) {
    return new SeqSelectExpr(
      Token.NoToken,
      true,
      definitions[Seq],
      definitions[Index],
      null,
      Token.NoToken);
  }
}

public class MapSelectExprConstraint : DefinitionConstraint {

  public readonly PartialValue Map;
  public readonly PartialValue Key;


  public MapSelectExprConstraint(PartialValue definedValue, PartialValue map, PartialValue key) : base(
    new List<PartialValue> { map, key }, definedValue, new List<Constraint> {
      new ContainmentConstraint(key, map, true)
    }) {
    Map = map;
    Key = key;
  }

  public override Expression RightHandSide(Dictionary<PartialValue, Expression> definitions) {
    return new SeqSelectExpr(Token.NoToken, true, definitions[Map], definitions[Key], null, Token.NoToken);
  }
}

public class SeqSelectExprWithLiteralConstraint : DefinitionConstraint {

  public readonly PartialValue Seq;
  public readonly LiteralExpr Index;


  public SeqSelectExprWithLiteralConstraint(PartialValue definedValue, PartialValue seq, LiteralExpr index) : base(
    new List<PartialValue> { seq }, definedValue,
    new List<Constraint> { new CardinalityGtThanLiteralConstraint(seq, index) }) {
    Seq = seq;
    Index = index;
  }

  public override Expression RightHandSide(Dictionary<PartialValue, Expression> definitions) {
    return new SeqSelectExpr(Token.NoToken, true, definitions[Seq], Index, null, Token.NoToken);
  }
}

public class CardinalityConstraint : DefinitionConstraint {

  public readonly PartialValue Collection;


  public CardinalityConstraint(PartialValue definedValue, PartialValue collection) : base(
    new List<PartialValue> { collection }, definedValue, new List<Constraint>()) {
    Collection = collection;
  }

  public override Expression RightHandSide(Dictionary<PartialValue, Expression> definitions) {
    return new UnaryOpExpr(Token.NoToken, UnaryOpExpr.Opcode.Cardinality, definitions[Collection]);
  }
}

public class SeqDisplayConstraint : DefinitionConstraint {
  private readonly List<PartialValue> elements;


  public SeqDisplayConstraint(PartialValue definedValue, List<PartialValue> elements) : base(elements, definedValue,
    new List<Constraint>()) {
    this.elements = elements;
  }

  public override Expression RightHandSide(Dictionary<PartialValue, Expression> definitions) {
    return new SeqDisplayExpr(Token.NoToken, elements.ConvertAll(element => definitions[element]));
  }
}

public class SetDisplayConstraint : Constraint {
  private readonly List<PartialValue> elements;
  private readonly PartialValue set;


  public SetDisplayConstraint(PartialValue set, List<PartialValue> elements) : base(elements.Append(set)) {
    this.elements = elements;
    this.set = set;
  }

  protected override Expression AsExpressionHelper(Dictionary<PartialValue, Expression> definitions) {
    var setDisplayExpr = new SetDisplayExpr(Token.NoToken, true, elements.ConvertAll(element => definitions[element]));
    setDisplayExpr.Type = set.Type;
    return new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, definitions[set], setDisplayExpr);
  }
}

public class MapKeysDisplayConstraint : Constraint {
  private readonly List<PartialValue> elements;
  private readonly PartialValue map;


  public MapKeysDisplayConstraint(PartialValue map, List<PartialValue> elements) : base(elements.Append(map)) {
    this.elements = elements;
    this.map = map;
  }

  protected override Expression AsExpressionHelper(Dictionary<PartialValue, Expression> definitions) {
    var setDisplayExpr = new SetDisplayExpr(Token.NoToken, true, elements.ConvertAll(element => definitions[element]));
    setDisplayExpr.Type = new SetType(true, map.Type.TypeArgs[0]);
    var memberSelectExpr = new MemberSelectExpr(Token.NoToken, definitions[map], new Name("Keys"));
    memberSelectExpr.Type = new SetType(true, map.Type.TypeArgs[0]);
    return new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, memberSelectExpr, setDisplayExpr);
  }
}

public class FunctionCallConstraint : DefinitionConstraint {
  private readonly List<PartialValue> args;
  private readonly PartialValue receiver;
  private readonly string functionName;


  public FunctionCallConstraint(
    PartialValue definedValue,
    PartialValue receiver,
    List<PartialValue> args,
    string functionName,
    bool receiverIsReferenceType) : base(args.Append(receiver), definedValue,
    receiverIsReferenceType
      ? new List<Constraint>
        { new NotNullConstraint(receiver), new FunctionCallRequiresConstraint(receiver, args, functionName) }
      : new List<Constraint> { new FunctionCallRequiresConstraint(receiver, args, functionName) }) {
    this.args = args;
    this.receiver = receiver;
    this.functionName = functionName;
  }

  public override Expression RightHandSide(Dictionary<PartialValue, Expression> definitions) {
    return new ApplySuffix(
      Token.NoToken,
      null,
      new ExprDotName(Token.NoToken, definitions[receiver], new Name(functionName), null),
      args.Select(formal =>
        new ActualBinding(null, definitions[formal])).ToList(),
      Token.NoToken);
  }
}

public class FunctionCallRequiresConstraint : Constraint {
  private readonly List<PartialValue> args;
  private readonly PartialValue receiver;
  private readonly string functionName;


  public FunctionCallRequiresConstraint(PartialValue receiver, List<PartialValue> args, string functionName)
    : base(args.Append(receiver), true) {
    this.args = args;
    this.receiver = receiver;
    this.functionName = functionName;
  }

  protected override Expression AsExpressionHelper(Dictionary<PartialValue, Expression> definitions) {
    return new ApplySuffix(
      Token.NoToken,
      null,
      new ExprDotName(Token.NoToken, definitions[receiver], new Name(functionName + ".requires"), null),
      args.Select(formal =>
        new ActualBinding(null, definitions[formal])).ToList(),
      Token.NoToken);
  }
}

public class ContainmentConstraint : Constraint {

  public readonly PartialValue Element, Set;
  public readonly bool IsIn;
  public ContainmentConstraint(PartialValue element, PartialValue set, bool isIn)
    : base(new List<PartialValue> { element, set }) {
    Element = element;
    Set = set;
    this.IsIn = isIn;
  }

  protected override Expression AsExpressionHelper(Dictionary<PartialValue, Expression> definitions) {
    return new BinaryExpr(
      Token.NoToken,
      IsIn ? BinaryExpr.Opcode.In : BinaryExpr.Opcode.NotIn,
      definitions[Element],
      definitions[Set]);
  }
}

public class ArrayLengthConstraint : Constraint {

  public PartialValue Array;
  public List<LiteralExpr> indices;

  public ArrayLengthConstraint(PartialValue array, List<LiteralExpr> indices)
    : base(new List<PartialValue> { array }) {
    Array = array;
    this.indices = indices;
  }

  protected override Expression AsExpressionHelper(Dictionary<PartialValue, Expression> definitions) {
    var length0 = new MemberSelectExpr(Token.NoToken, definitions[Array], new Name(indices.Count == 1 ? "Length" : "Length0"));
    length0.Type = Type.Int;
    var constraint = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Gt, length0, indices.First());
    constraint.Type = Type.Bool;
    for (int i = 1; i < indices.Count; i++) {
      var length = new MemberSelectExpr(Token.NoToken, definitions[Array], new Name($"Length{i}"));
      length.Type = Type.Int;
      var newConstraint = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Gt, length, indices[i]);
      newConstraint.Type = Type.Bool;
      constraint = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, constraint, newConstraint);
      constraint.Type = Type.Bool;
    }
    return constraint;
  }
}

public class NeqConstraint : Constraint {
  private readonly PartialValue value;
  private readonly PartialValue neq;
  public NeqConstraint(PartialValue value, PartialValue neq) : base(new List<PartialValue> { value, neq }) {
    this.value = value;
    this.neq = neq;
  }

  protected override Expression AsExpressionHelper(Dictionary<PartialValue, Expression> definitions) {
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

  public DatatypeConstructorCheckConstraint(PartialValue obj, string constructorName)
    : base(new List<PartialValue> { obj }) {
    this.obj = obj;
    ConstructorName = constructorName;
  }

  protected override Expression AsExpressionHelper(Dictionary<PartialValue, Expression> definitions) {
    return new MemberSelectExpr(Token.NoToken, definitions[obj], new Name(ConstructorName + "?"));
  }
}

public class CardinalityGtThanConstraint : Constraint {
  private readonly PartialValue collection;
  private readonly PartialValue bound;

  public CardinalityGtThanConstraint(PartialValue collection, PartialValue bound)
    : base(new List<PartialValue> { collection, bound }) {
    this.collection = collection;
    this.bound = bound;
  }

  protected override Expression AsExpressionHelper(Dictionary<PartialValue, Expression> definitions) {
    var cardinalityExpr = new UnaryOpExpr(Token.NoToken, UnaryOpExpr.Opcode.Cardinality, definitions[collection]) {
      Type = Type.Int
    };
    return new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Gt, cardinalityExpr, definitions[bound]);
  }
}

public class CardinalityGtThanLiteralConstraint : Constraint {
  private readonly PartialValue collection;
  private readonly LiteralExpr bound;

  public CardinalityGtThanLiteralConstraint(PartialValue collection, LiteralExpr bound)
    : base(new List<PartialValue> { collection }) {
    this.collection = collection;
    this.bound = bound;
  }

  protected override Expression AsExpressionHelper(Dictionary<PartialValue, Expression> definitions) {
    var cardinalityExpr = new UnaryOpExpr(Token.NoToken, UnaryOpExpr.Opcode.Cardinality, definitions[collection]) {
      Type = Type.Int
    };
    return new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Gt, cardinalityExpr, bound);
  }
}

public class TypeTestConstraint : Constraint {
  public readonly Type Type;
  private readonly PartialValue value;
  public TypeTestConstraint(PartialValue value, Type type) : base(new List<PartialValue> { value }) {
    Type = type;
    this.value = value;
  }

  protected override Expression AsExpressionHelper(Dictionary<PartialValue, Expression> definitions) {
    return new TypeTestExpr(Token.NoToken, definitions[value], Type);
  }
}

public class NotNullConstraint : Constraint {
  private readonly PartialValue value;

  public NotNullConstraint(PartialValue value) : base(new List<PartialValue> { value }) {
    this.value = value;
  }

  protected override Expression AsExpressionHelper(Dictionary<PartialValue, Expression> definitions) {
    var nullValue = new LiteralExpr(Token.NoToken) {
      Type = new InferredTypeProxy()
    };
    return new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Neq, definitions[value], nullValue);
  }
}