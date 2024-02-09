using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny.LanguageServer.CounterExampleGeneration;

public abstract class Constraint {
  public readonly List<PartialValue> referencedValues;
  public IEnumerable<PartialValue> ReferencedValues => referencedValues.AsEnumerable();

  public Constraint(IEnumerable<PartialValue> referencedValues) {
    this.referencedValues = referencedValues.ToList();
  }

  public Expression AsExpression(Dictionary<PartialValue, Expression> definitions, bool wrapDefinitions) {
    var expression = AsExpression(definitions);
    if (this is not DefinitionConstraint definitionConstraint) {
      expression.Type = Type.Bool;
      return expression;
    }
    expression.Type = definitionConstraint.definedValue.Type;
    if (!wrapDefinitions) {
      return expression;
    }
    expression = definitionConstraint.WrapDefinition(definitions, expression);
    var wellFormedNessConstraint = definitionConstraint.WellFormedNessCondition(definitions);
    if (wellFormedNessConstraint == null) {
      return expression;
    }
    wellFormedNessConstraint.Type = Type.Bool;
    expression = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, wellFormedNessConstraint, expression);
    expression.Type = Type.Bool;
    return expression;
  }
  
  protected abstract Expression AsExpression(Dictionary<PartialValue, Expression> definitions);
  

  public static void FindDefinitions(Dictionary<PartialValue, Expression> knownDefinitions, List<Constraint> constraints, bool allowNewIdentifiers) {
    // TODO: Need to make sure the wellformedness checks make it to the final expression
    // TODO: Remove duplicate assignemnts and inconsistent properties
    var foundANewDefinition = true;
    var oldConstraints = new List<Constraint>();
    oldConstraints.AddRange(constraints);
    constraints.Clear();
    while (foundANewDefinition) {
      foundANewDefinition = false;
      foreach (var constraint in oldConstraints.Where(constraint => allowNewIdentifiers || constraint is not IdentifierExprConstraint)) {
        if (!constraints.Contains(constraint) && constraint is not DefinitionConstraint && constraint.ReferencedValues.All(knownDefinitions.ContainsKey)) {
          constraints.Add(constraint);
          foundANewDefinition = true;
          break;
        }
      }
      foreach (var constraint in oldConstraints.Where(constraint => allowNewIdentifiers || constraint is not IdentifierExprConstraint)) { // First add as constraints the literal expressions
        if (constraint is DefinitionConstraint definition && !knownDefinitions.ContainsKey(definition.definedValue) &&
            !constraint.ReferencedValues.Any()) {
          constraints.Add(constraint);
          knownDefinitions[definition.definedValue] = definition.AsExpression(knownDefinitions, false);
         foundANewDefinition = true;
          break;
        }
      }
      if (foundANewDefinition) { continue; }
      foreach (var constraint in oldConstraints.Where(constraint => allowNewIdentifiers || constraint is not IdentifierExprConstraint)) {
        if (constraint is DefinitionConstraint definition && !knownDefinitions.ContainsKey(definition.definedValue) &&
            constraint.ReferencedValues.All(knownDefinitions.ContainsKey) && constraint.ReferencedValues.Any()) {
          constraints.Add(constraint);
          knownDefinitions[definition.definedValue] = definition.AsExpression(knownDefinitions, false);
          foundANewDefinition = true;
          break;
        }
      }
    }
    foreach (var constraint in oldConstraints.Where(constraint => allowNewIdentifiers || constraint is not IdentifierExprConstraint)) {
      if (!constraints.Contains(constraint) && constraint is not DefinitionConstraint) {
        constraints.Add(constraint);
      }
    }
    foreach (var constraint in oldConstraints.Where(constraint => allowNewIdentifiers || constraint is not IdentifierExprConstraint)) {
      if (!constraints.Contains(constraint) && constraint is DefinitionConstraint) {
        constraints.Add(constraint);
      }
    }
  }

}

public abstract class DefinitionConstraint : Constraint {

  public readonly PartialValue definedValue;
  public DefinitionConstraint(IEnumerable<PartialValue> referencedValues, PartialValue definedValue) : base(referencedValues) {
    this.definedValue = definedValue;
  }

  internal Expression WrapDefinition(Dictionary<PartialValue, Expression> definitions, Expression expression) {
    var binaryExpr = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Eq, definitions[definedValue], expression);
    binaryExpr.Type = Type.Bool;
    return binaryExpr;
  }

  public abstract Expression? WellFormedNessCondition(Dictionary<PartialValue, Expression> definitions);
}

public class IdentifierExprConstraint : DefinitionConstraint {

  public readonly string name;
  
  public IdentifierExprConstraint(PartialValue definedValue, string name) : base(new List<PartialValue>(), definedValue) {
    this.name = name;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new IdentifierExpr(Token.NoToken, name);
  }

  public override Expression? WellFormedNessCondition(Dictionary<PartialValue, Expression> definitions) {
    return null;
  }
}

public class LiteralExprConstraint : DefinitionConstraint {

  public readonly Expression LiteralExpr;
  public LiteralExprConstraint(PartialValue definedValue, Expression literalExpr) : base(new List<PartialValue>(), definedValue) {
    this.LiteralExpr = literalExpr;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return LiteralExpr;
  }

  public override Expression? WellFormedNessCondition(Dictionary<PartialValue, Expression> definitions) {
    return null;
  }
}

public abstract class MemberSelectExprConstraint : DefinitionConstraint {

  public readonly PartialValue Obj;
  public readonly string MemberName;

  public MemberSelectExprConstraint(PartialValue definedValue, PartialValue Obj, string memberName) : base(new List<PartialValue>() {Obj}, definedValue) {
    this.Obj = Obj;
    this.MemberName = memberName;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new MemberSelectExpr(Token.NoToken, definitions[Obj], MemberName);
  }
}

public class MemberSelectExprDatatypeConstraint : MemberSelectExprConstraint {
  public MemberSelectExprDatatypeConstraint(PartialValue definedValue, PartialValue Obj, string memberName) : base(
    definedValue, Obj, memberName) {
  }
  public override Expression? WellFormedNessCondition(Dictionary<PartialValue, Expression> definitions) {
    return null;
  }
}

public class MemberSelectExprClassConstraint : MemberSelectExprConstraint {
  public MemberSelectExprClassConstraint(PartialValue definedValue, PartialValue Obj, string memberName) : base(
    definedValue, Obj, memberName) {
  }
  public override Expression? WellFormedNessCondition(Dictionary<PartialValue, Expression> definitions) {
    var nullValue = new LiteralExpr(Token.NoToken);
    nullValue.Type = new InferredTypeProxy();
    return new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Neq, definitions[Obj], nullValue);
  }
}

public class DatatypeValueConstraint : DefinitionConstraint {

  public readonly IEnumerable<PartialValue> UnnamedDestructors;
  public readonly string constructorName;
  public readonly string datatypeName;

  public DatatypeValueConstraint(PartialValue definedValue, string datatypeName, string constructorName, List<PartialValue> unnamedDestructors) : base(unnamedDestructors, definedValue) {
    this.UnnamedDestructors = unnamedDestructors;
    this.constructorName = constructorName;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new DatatypeValue(Token.NoToken, datatypeName,
      constructorName,
      UnnamedDestructors.Select(destructor => definitions[destructor]).ToList());
  }

  public override Expression? WellFormedNessCondition(Dictionary<PartialValue, Expression> definitions) {
    return null;
  }
}

public class SeqSelectExprConstraint : DefinitionConstraint {

  public readonly PartialValue Seq;
  public readonly PartialValue Index;
  

  public SeqSelectExprConstraint(PartialValue definedValue, PartialValue Seq, PartialValue Index) : base(new List<PartialValue>() {Seq, Index}, definedValue) {
    this.Seq = Seq;
    this.Index = Index;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new SeqSelectExpr(Token.NoToken, true, definitions[Seq], definitions[Index], null, Token.NoToken);
  }

  public override Expression? WellFormedNessCondition(Dictionary<PartialValue, Expression> definitions) {
    var cardinalityExpr = new UnaryOpExpr(Token.NoToken, UnaryOpExpr.Opcode.Cardinality, definitions[Seq]);
    cardinalityExpr.Type = Seq.Type;
    return new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Gt, cardinalityExpr, definitions[Index]);
  }
}

public class SeqSelectExprArrayConstraint : DefinitionConstraint {

  public readonly PartialValue Array;
  public readonly string index;
  

  public SeqSelectExprArrayConstraint(PartialValue definedValue, PartialValue Array, string Index) : base(new List<PartialValue>() {Array}, definedValue) {
    this.Array = Array;
    this.index = Index;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new SeqSelectExpr(Token.NoToken, true, definitions[Array], new NameSegment(Token.NoToken, index, null), null, Token.NoToken);
  }

  public override Expression? WellFormedNessCondition(Dictionary<PartialValue, Expression> definitions) {
    // TODO
    return null;
  }
}

public class MapSelectExprConstraint : DefinitionConstraint {

  public readonly PartialValue Map;
  public readonly PartialValue Key;
  

  public MapSelectExprConstraint(PartialValue definedValue, PartialValue Map, PartialValue Key) : base(new List<PartialValue>() {Map, Key}, definedValue) {
    this.Map = Map;
    this.Key = Key;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new SeqSelectExpr(Token.NoToken, true, definitions[Map], definitions[Key], null, Token.NoToken);
  }

  public override Expression? WellFormedNessCondition(Dictionary<PartialValue, Expression> definitions) {
    return new BinaryExpr(
      Token.NoToken,
      BinaryExpr.Opcode.In,
      definitions[Key],
      definitions[Map]);
  }
}

public class SeqSelectExprWithLiteralConstraint : DefinitionConstraint {

  public readonly PartialValue Seq;
  public readonly LiteralExpr Index;
  

  public SeqSelectExprWithLiteralConstraint(PartialValue definedValue, PartialValue Seq, LiteralExpr Index) : base(new List<PartialValue>() {Seq}, definedValue) {
    this.Seq = Seq;
    this.Index = Index;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new SeqSelectExpr(Token.NoToken, true, definitions[Seq], Index, null, Token.NoToken);
  }

  public override Expression? WellFormedNessCondition(Dictionary<PartialValue, Expression> definitions) {
    var cardinalityExpr = new UnaryOpExpr(Token.NoToken, UnaryOpExpr.Opcode.Cardinality, definitions[Seq]);
    cardinalityExpr.Type = Seq.Type;
    return new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Gt, cardinalityExpr, Index);
  }
}

public class CardinalityConstraint : DefinitionConstraint {

  public readonly PartialValue Collection;
  

  public CardinalityConstraint(PartialValue definedValue, PartialValue collection) : base(new List<PartialValue>() {collection}, definedValue) {
    this.Collection = collection;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new UnaryOpExpr(Token.NoToken, UnaryOpExpr.Opcode.Cardinality, definitions[Collection]);
  }

  public override Expression? WellFormedNessCondition(Dictionary<PartialValue, Expression> definitions) {
    return null;
  }
}

public class SeqDisplayConstraint : DefinitionConstraint {

  public readonly List<PartialValue> elements;
  

  public SeqDisplayConstraint(PartialValue definedValue, List<PartialValue> elements) : base(elements, definedValue) {
    this.elements = elements;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new SeqDisplayExpr(Token.NoToken, elements.ConvertAll(element => definitions[element]));
  }

  public override Expression? WellFormedNessCondition(Dictionary<PartialValue, Expression> definitions) {
    return null;
  }
}

public class ContainmentConstraint : Constraint {

  public readonly PartialValue element, set;
  public readonly bool isIn;
  public ContainmentConstraint(PartialValue element, PartialValue set, bool isIn) : base(new List<PartialValue>() {element, set}) {
    this.element = element;
    this.set = set;
    this.isIn = isIn;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new BinaryExpr(
      Token.NoToken,
      isIn ? BinaryExpr.Opcode.In : BinaryExpr.Opcode.NotIn,
      definitions[element],
      definitions[set]);
  }
}

public class NeqConstraint : Constraint {

  public readonly PartialValue value;
  public readonly PartialValue Neq;
  public NeqConstraint(PartialValue value, PartialValue Neq) : base(new List<PartialValue>() {value, Neq}) {
    this.value = value;
    this.Neq = Neq;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new BinaryExpr(
      Token.NoToken,
      BinaryExpr.Opcode.Neq,
      definitions[value],
      definitions[Neq]);
  }
}


public class DatatypeConstructorCheckConstraint : Constraint {

  public readonly PartialValue Obj;
  public readonly string constructorName;

  public DatatypeConstructorCheckConstraint(PartialValue Obj, string constructorName) : base(new List<PartialValue>() {Obj}) {
    this.Obj = Obj;
    this.constructorName = constructorName;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new MemberSelectExpr(Token.NoToken, definitions[Obj], constructorName);
  }
}

public class EmptyConstraint : Constraint {

  public readonly PartialValue Collection;

  public EmptyConstraint(PartialValue collection) : base(new List<PartialValue>() {collection}) {
    this.Collection = collection;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    var zero = new LiteralExpr(Token.NoToken, 0);
    zero.Type = Type.Int;
    return new UnaryOpExpr(Token.NoToken, UnaryOpExpr.Opcode.Cardinality, definitions[Collection]);
  }
}

public class TypeTestConstraint : Constraint {

  public readonly Type type;
  public readonly PartialValue Value;
  public TypeTestConstraint(PartialValue value, Type type) : base(new List<PartialValue>() {value}) {
    this.type = type;
    this.Value = value;
  }

  protected override Expression AsExpression(Dictionary<PartialValue, Expression> definitions) {
    return new TypeTestExpr(Token.NoToken, definitions[Value], type);
  }
}
