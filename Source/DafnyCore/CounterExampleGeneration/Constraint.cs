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

public class IdentifierExprConstraint(PartialValue definedValue, string name)
  : DefinitionConstraint(new List<PartialValue>(), definedValue, []) {
  public override Expression RightHandSide(Dictionary<PartialValue, Expression> definitions) {
    return new IdentifierExpr(Token.NoToken, name);
  }
}

public class ArraySelectionConstraint(PartialValue definedValue, PartialValue array, List<LiteralExpr> indices)
  : DefinitionConstraint(new List<PartialValue>() { array }, definedValue,
    [new ArrayLengthConstraint(array, indices)]) {
  public PartialValue Array = array;
  public List<LiteralExpr> indices = indices;

  public override Expression RightHandSide(Dictionary<PartialValue, Expression> definitions) {
    if (indices.Count == 1) {
      return new SeqSelectExpr(Token.NoToken, true, definitions[Array], indices.First(), null, Token.NoToken);
    }
    return new MultiSelectExpr(Token.NoToken, definitions[Array], indices.OfType<Expression>().ToList());
  }
}

public class LiteralExprConstraint(PartialValue definedValue, Expression literalExpr)
  : DefinitionConstraint(new List<PartialValue>(), definedValue, []) {

  public readonly Expression LiteralExpr = literalExpr;

  public override Expression RightHandSide(Dictionary<PartialValue, Expression> definitions) {
    return LiteralExpr;
  }
}

public abstract class MemberSelectExprConstraint(
  PartialValue definedValue,
  PartialValue obj,
  string memberName,
  List<Constraint> constraint)
  : DefinitionConstraint(new List<PartialValue> { obj }, definedValue, constraint) {

  public readonly PartialValue Obj = obj;
  public readonly string MemberName = memberName;

  public override Expression RightHandSide(Dictionary<PartialValue, Expression> definitions) {
    return new MemberSelectExpr(Token.NoToken, definitions[Obj], new Name(MemberName));
  }
}

public class MemberSelectExprDatatypeConstraint(PartialValue definedValue, PartialValue obj, string memberName)
  : MemberSelectExprConstraint(definedValue, obj, memberName, []);

public class MemberSelectExprClassConstraint(PartialValue definedValue, PartialValue obj, string memberName)
  : MemberSelectExprConstraint(definedValue, obj, memberName, [new NotNullConstraint(obj)]);

public class DatatypeValueConstraint(
  PartialValue definedValue,
  string datatypeName,
  string constructorName,
  IReadOnlyCollection<PartialValue> unnamedDestructors)
  : DefinitionConstraint(unnamedDestructors, definedValue, []) {

  public readonly IEnumerable<PartialValue> UnnamedDestructors = unnamedDestructors;

  public override Expression RightHandSide(Dictionary<PartialValue, Expression> definitions) {
    return new DatatypeValue(Token.NoToken, datatypeName,
      constructorName,
      UnnamedDestructors.Select(destructor => definitions[destructor]).ToList());
  }
}

public class SeqSelectExprConstraint(PartialValue definedValue, PartialValue seq, PartialValue index)
  : DefinitionConstraint(new List<PartialValue> { seq, index }, definedValue,
    [new CardinalityGtThanConstraint(seq, index)]) {

  public readonly PartialValue Seq = seq;
  public readonly PartialValue Index = index;


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

public class MapSelectExprConstraint(PartialValue definedValue, PartialValue map, PartialValue key)
  : DefinitionConstraint(new List<PartialValue> { map, key }, definedValue,
    [new ContainmentConstraint(key, map, true)]) {

  public readonly PartialValue Map = map;
  public readonly PartialValue Key = key;


  public override Expression RightHandSide(Dictionary<PartialValue, Expression> definitions) {
    return new SeqSelectExpr(Token.NoToken, true, definitions[Map], definitions[Key], null, Token.NoToken);
  }
}

public class SeqSelectExprWithLiteralConstraint(PartialValue definedValue, PartialValue seq, LiteralExpr index)
  : DefinitionConstraint(new List<PartialValue> { seq }, definedValue,
    [new CardinalityGtThanLiteralConstraint(seq, index)]) {

  public readonly PartialValue Seq = seq;
  public readonly LiteralExpr Index = index;


  public override Expression RightHandSide(Dictionary<PartialValue, Expression> definitions) {
    return new SeqSelectExpr(Token.NoToken, true, definitions[Seq], Index, null, Token.NoToken);
  }
}

public class CardinalityConstraint(PartialValue definedValue, PartialValue collection)
  : DefinitionConstraint(new List<PartialValue> { collection }, definedValue, []) {

  public readonly PartialValue Collection = collection;


  public override Expression RightHandSide(Dictionary<PartialValue, Expression> definitions) {
    return new UnaryOpExpr(Token.NoToken, UnaryOpExpr.Opcode.Cardinality, definitions[Collection]);
  }
}

public class SeqDisplayConstraint(PartialValue definedValue, List<PartialValue> elements) : DefinitionConstraint(
  elements, definedValue,
  []) {
  public override Expression RightHandSide(Dictionary<PartialValue, Expression> definitions) {
    return new SeqDisplayExpr(Token.NoToken, elements.ConvertAll(element => definitions[element]));
  }
}

public class SetDisplayConstraint(PartialValue set, List<PartialValue> elements) : Constraint(elements.Append(set)) {
  protected override Expression AsExpressionHelper(Dictionary<PartialValue, Expression> definitions) {
    var setDisplayExpr = new SetDisplayExpr(Token.NoToken, true, elements.ConvertAll(element => definitions[element]));
    setDisplayExpr.Type = set.Type;
    return new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, definitions[set], setDisplayExpr);
  }
}

public class MapKeysDisplayConstraint(PartialValue map, List<PartialValue> elements)
  : Constraint(elements.Append(map)) {
  protected override Expression AsExpressionHelper(Dictionary<PartialValue, Expression> definitions) {
    var setDisplayExpr = new SetDisplayExpr(Token.NoToken, true, elements.ConvertAll(element => definitions[element]));
    setDisplayExpr.Type = new SetType(true, map.Type.TypeArgs[0]);
    var memberSelectExpr = new MemberSelectExpr(Token.NoToken, definitions[map], new Name("Keys"));
    memberSelectExpr.Type = new SetType(true, map.Type.TypeArgs[0]);
    return new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, memberSelectExpr, setDisplayExpr);
  }
}

public class FunctionCallConstraint(
  PartialValue definedValue,
  PartialValue receiver,
  List<PartialValue> args,
  string functionName,
  bool receiverIsReferenceType)
  : DefinitionConstraint(args.Append(receiver), definedValue,
    receiverIsReferenceType
      ? [new NotNullConstraint(receiver), new FunctionCallRequiresConstraint(receiver, args, functionName)]
      : [new FunctionCallRequiresConstraint(receiver, args, functionName)]) {
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

public class FunctionCallRequiresConstraint(PartialValue receiver, List<PartialValue> args, string functionName)
  : Constraint(args.Append(receiver), true) {
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

public class ContainmentConstraint(PartialValue element, PartialValue set, bool isIn)
  : Constraint(new List<PartialValue> { element, set }) {

  public readonly PartialValue Element = element, Set = set;
  public readonly bool IsIn = isIn;

  protected override Expression AsExpressionHelper(Dictionary<PartialValue, Expression> definitions) {
    return new BinaryExpr(
      Token.NoToken,
      IsIn ? BinaryExpr.Opcode.In : BinaryExpr.Opcode.NotIn,
      definitions[Element],
      definitions[Set]);
  }
}

public class ArrayLengthConstraint(PartialValue array, List<LiteralExpr> indices)
  : Constraint(new List<PartialValue> { array }) {

  public PartialValue Array = array;
  public List<LiteralExpr> indices = indices;

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

public class NeqConstraint(PartialValue value, PartialValue neq) : Constraint(new List<PartialValue> { value, neq }) {
  protected override Expression AsExpressionHelper(Dictionary<PartialValue, Expression> definitions) {
    return new BinaryExpr(
      Token.NoToken,
      BinaryExpr.Opcode.Neq,
      definitions[value],
      definitions[neq]);
  }
}


public class DatatypeConstructorCheckConstraint(PartialValue obj, string constructorName)
  : Constraint(new List<PartialValue> { obj }) {
  public readonly string ConstructorName = constructorName;

  protected override Expression AsExpressionHelper(Dictionary<PartialValue, Expression> definitions) {
    return new MemberSelectExpr(Token.NoToken, definitions[obj], new Name(ConstructorName + "?"));
  }
}

public class CardinalityGtThanConstraint(PartialValue collection, PartialValue bound)
  : Constraint(new List<PartialValue> { collection, bound }) {
  protected override Expression AsExpressionHelper(Dictionary<PartialValue, Expression> definitions) {
    var cardinalityExpr = new UnaryOpExpr(Token.NoToken, UnaryOpExpr.Opcode.Cardinality, definitions[collection]) {
      Type = Type.Int
    };
    return new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Gt, cardinalityExpr, definitions[bound]);
  }
}

public class CardinalityGtThanLiteralConstraint(PartialValue collection, LiteralExpr bound)
  : Constraint(new List<PartialValue> { collection }) {
  protected override Expression AsExpressionHelper(Dictionary<PartialValue, Expression> definitions) {
    var cardinalityExpr = new UnaryOpExpr(Token.NoToken, UnaryOpExpr.Opcode.Cardinality, definitions[collection]) {
      Type = Type.Int
    };
    return new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Gt, cardinalityExpr, bound);
  }
}

public class TypeTestConstraint(PartialValue value, Type type) : Constraint(new List<PartialValue> { value }) {
  public readonly Type Type = type;

  protected override Expression AsExpressionHelper(Dictionary<PartialValue, Expression> definitions) {
    return new TypeTestExpr(Token.NoToken, definitions[value], Type);
  }
}

public class NotNullConstraint(PartialValue value) : Constraint(new List<PartialValue> { value }) {
  protected override Expression AsExpressionHelper(Dictionary<PartialValue, Expression> definitions) {
    var nullValue = new LiteralExpr(Token.NoToken) {
      Type = new InferredTypeProxy()
    };
    return new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Neq, definitions[value], nullValue);
  }
}