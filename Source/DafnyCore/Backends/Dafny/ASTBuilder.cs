using System;
using System.Collections.Generic;
using System.Numerics;
using Dafny;
using DAST;
using DAST.Format;
using JetBrains.Annotations;
using Microsoft.CodeAnalysis;
using Microsoft.Dafny.Compilers;
using Std.Wrappers;
using Attribute = DAST.Attribute;

namespace Microsoft.Dafny.Compilers {

  interface Container {
    public void AddUnsupported(string why);
  }

  class ProgramBuilder : ModuleContainer {
    readonly List<Module> items = [];

    public void AddModule(Module item) {
      items.Add(item);
    }

    public List<Module> Finish() {
      return items;
    }

    public void AddUnsupported(string why) {
      items.Add(ModuleContainer.UnsupportedToModule(why));
    }
  }

  interface ModuleContainer : Container {
    void AddModule(Module item);

    public ModuleBuilder Module(string name, string docString, Sequence<Attribute> attributes, bool requiresExterns) {
      return new ModuleBuilder(this, name, docString, attributes, requiresExterns);
    }

    public static Module UnsupportedToModule(string why) {
      return new Module(
        Sequence<Rune>.UnicodeFromString($"uncompilable/*{why.Replace(".", ",")}*/"),
        Sequence<Rune>.UnicodeFromString(""),
        Sequence<Attribute>.FromElements(
          (Attribute)Attribute.create_Attribute(
            Sequence<Rune>.UnicodeFromString("extern"),
            Sequence<Sequence<Rune>>.FromElements(
              (Sequence<Rune>)Sequence<Rune>.UnicodeFromString($"uncompilable/*{why}*/")))), false,
        Std.Wrappers.Option<Sequence<ModuleItem>>.create_None());
    }
  }

  class ModuleBuilder(
    ModuleContainer parent,
    string name,
    string docString,
    Sequence<Attribute> attributes,
    bool requiresExterns)
    : ClassContainer, TraitContainer, NewtypeContainer, DatatypeContainer, SynonymTypeContainer {
    readonly List<ModuleItem> body = [];

    public void AddModule(Module item) {
      body.Add((ModuleItem)ModuleItem.create_Module(item));
    }

    public void AddClass(Class item) {
      body.Add((ModuleItem)ModuleItem.create_Class(item));
    }

    public void AddTrait(Trait item) {
      body.Add((ModuleItem)ModuleItem.create_Trait(item));
    }

    public void AddNewtype(Newtype item) {
      body.Add((ModuleItem)ModuleItem.create_Newtype(item));
    }

    public void AddDatatype(Datatype item) {
      body.Add((ModuleItem)ModuleItem.create_Datatype(item));
    }

    public object Finish() {
      parent.AddModule((Module)Module.create(
        Sequence<Rune>.UnicodeFromString(name),
        Sequence<Rune>.UnicodeFromString(docString),
        attributes,
        requiresExterns,
        Std.Wrappers.Option<Sequence<ModuleItem>>.create_Some((Sequence<ModuleItem>)Sequence<ModuleItem>.FromArray(body.ToArray()))
      ));

      return parent;
    }

    public void AddSynonymType(SynonymType item) {
      body.Add((ModuleItem)ModuleItem.create_SynonymType(item));
    }

    public void AddUnsupported(string why) {
      body.Add((ModuleItem)ModuleItem.create_Module(ModuleContainer.UnsupportedToModule(why)));
    }
  }

  interface ClassContainer : Container {
    void AddClass(Class item);

    public ClassBuilder Class(string name, string enclosingModule, List<DAST.TypeArgDecl> typeParams, List<DAST.Type> superClasses, ISequence<_IAttribute> attributes, string docString) {
      return new ClassBuilder(this, name, docString, enclosingModule, typeParams, superClasses, attributes);
    }
  }



  class ClassBuilder(
    ClassContainer parent,
    string name,
    string docString,
    string enclosingModule,
    List<DAST.TypeArgDecl> typeParams,
    List<DAST.Type> superClasses,
    ISequence<_IAttribute> attributes)
    : ClassLike {
    readonly List<DAST.Field> fields = [];
    readonly List<DAST.Method> body = [];

    public void AddMethod(DAST.Method item) {
      body.Add(item);
    }

    public void AddField(DAST.Formal item, bool isConstant, _IOption<DAST._IExpression> defaultValue, bool isStatic) {
      fields.Add((DAST.Field)DAST.Field.create_Field(item, isConstant, defaultValue, isStatic));
    }

    public object Finish() {
      parent.AddClass((Class)Class.create(
        Sequence<Rune>.UnicodeFromString(name),
        Sequence<Rune>.UnicodeFromString(docString),
        Sequence<Rune>.UnicodeFromString(enclosingModule),
        Sequence<DAST.TypeArgDecl>.FromArray(typeParams.ToArray()),
        Sequence<DAST.Type>.FromArray(superClasses.ToArray()),
        Sequence<DAST.Field>.FromArray(this.fields.ToArray()),
        Sequence<DAST.Method>.FromArray(body.ToArray()),
        attributes
      ));
      return parent;
    }
  }

  interface TraitContainer : Container {
    void AddTrait(Trait item);

    public TraitBuilder Trait(string name, List<DAST.TypeArgDecl> typeParams, List<DAST.Type> parents,
      ISequence<_IAttribute> attributes, string docString, _ITraitType traitType) {
      return new TraitBuilder(this, name, docString, typeParams, parents, attributes, traitType);
    }
  }

  class TraitBuilder(
    TraitContainer parent,
    string name,
    string docString,
    List<DAST.TypeArgDecl> typeParams,
    List<DAST.Type> parents,
    ISequence<_IAttribute> attributes,
    _ITraitType traitType)
    : ClassLike {
    readonly List<DAST.Method> body = [];

    public void AddMethod(DAST.Method item) {
      // remove existing method with the same name, because we're going to define an implementation
      for (int i = 0; i < body.Count; i++) {
        if (body[i].is_Method && body[i].dtor_name.Equals(item.dtor_name)) {
          body.RemoveAt(i);
          break;
        }
      }

      body.Add(item);
    }

    public void AddField(DAST.Formal item, bool isConstant, _IOption<DAST._IExpression> defaultValue, bool isStatic) {
      parent.AddUnsupported("var/const fro trait - " + item.dtor_name);
    }

    public object Finish() {
      parent.AddTrait((Trait)Trait.create(
        Sequence<Rune>.UnicodeFromString(name),
        Sequence<Rune>.UnicodeFromString(docString),
        Sequence<DAST.TypeArgDecl>.FromArray(typeParams.ToArray()),
        traitType,
        Sequence<DAST.Type>.FromArray(parents.ToArray()),
        Sequence<DAST.Method>.FromArray(body.ToArray()),
        attributes)
      );
      return parent;
    }
  }

  interface NewtypeContainer : Container {
    void AddNewtype(Newtype item);

    public NewtypeBuilder Newtype(string name, List<DAST.TypeArgDecl> typeParams,
      DAST.Type baseType, NewtypeRange newtypeRange, Option<DAST.NewtypeConstraint> constraint, List<DAST.Statement> witnessStmts, DAST.Expression witness,
      ISequence<_IAttribute> attributes, string docString) {
      return new NewtypeBuilder(this, name, typeParams, newtypeRange, baseType, constraint, witnessStmts, witness, attributes, docString);
    }
  }

  class NewtypeBuilder(
    NewtypeContainer parent,
    string name,
    List<TypeArgDecl> typeParams,
    NewtypeRange newtypeRange,
    DAST.Type baseType,
    Option<DAST.NewtypeConstraint> constraint,
    List<DAST.Statement> statements,
    DAST.Expression witness,
    ISequence<_IAttribute> attributes,
    string docString)
    : ClassLike {
    private readonly List<DAST._IMethod> methods = [];

    public void AddMethod(DAST.Method item) {
      methods.Add(item);
    }

    public void AddField(DAST.Formal item, bool isConstant, _IOption<DAST._IExpression> defaultValue, bool isStatic) {
      parent.AddUnsupported("Newtype field " + item.dtor_name);
    }

    public object Finish() {
      parent.AddNewtype((Newtype)Newtype.create(
        Sequence<Rune>.UnicodeFromString(name),
        Sequence<Rune>.UnicodeFromString(docString),
        Sequence<DAST.TypeArgDecl>.FromArray(typeParams.ToArray()),
        baseType,
        newtypeRange,
        constraint,
        Sequence<DAST.Statement>.FromArray(statements.ToArray()),
        witness == null
          ? Option<DAST._IExpression>.create_None()
          : Option<DAST._IExpression>.create_Some(witness),
        attributes,
        Sequence<DAST._IMethod>.FromArray(methods.ToArray())
      ));
      return parent;
    }
  }

  interface SynonymTypeContainer : Container {
    void AddSynonymType(SynonymType item);

    public SynonymTypeBuilder SynonymType(string name, List<DAST.TypeArgDecl> typeParams,
      DAST.Type rhsType, List<DAST.Statement> witnessStmts, DAST.Expression witness,
      ISequence<_IAttribute> attributes, string docString) {
      return new SynonymTypeBuilder(this, name, typeParams, rhsType, witnessStmts, witness, attributes, docString);
    }
  }

  class SynonymTypeBuilder(
    SynonymTypeContainer parent,
    string name,
    List<DAST.TypeArgDecl> typeParams,
    DAST.Type rhsType,
    List<DAST.Statement> statements,
    DAST.Expression witness,
    ISequence<_IAttribute> attributes,
    string docString) {
    public object Finish() {
      parent.AddSynonymType((SynonymType)SynonymType.create(
        Sequence<Rune>.UnicodeFromString(name),
        Sequence<Rune>.UnicodeFromString(docString),
        Sequence<DAST.TypeArgDecl>.FromArray(typeParams.ToArray()),
        rhsType,
        Sequence<DAST.Statement>.FromArray(statements.ToArray()),
        witness == null
          ? Option<DAST._IExpression>.create_None()
          : Option<DAST._IExpression>.create_Some(witness),
        attributes
      ));
      return parent;
    }
  }

  interface DatatypeContainer : Container {
    void AddDatatype(Datatype item);

    public DatatypeBuilder Datatype(string name, string enclosingModule, List<DAST.TypeArgDecl> typeParams,
      List<DAST.DatatypeCtor> ctors, bool isCo, ISequence<_IAttribute> attributes, string docString, List<DAST.Type> superTraitTypes) {
      return new DatatypeBuilder(this, name, docString, enclosingModule, typeParams, ctors, isCo, attributes, superTraitTypes);
    }
  }

  class DatatypeBuilder(
    DatatypeContainer parent,
    string name,
    string docString,
    string enclosingModule,
    List<DAST.TypeArgDecl> typeParams,
    List<DAST.DatatypeCtor> ctors,
    bool isCo,
    ISequence<_IAttribute> attributes,
    List<DAST.Type> superTraitTypes)
    : ClassLike {
    readonly List<DAST.Method> body = [];

    public void AddMethod(DAST.Method item) {
      body.Add(item);
    }

    public void AddField(DAST.Formal item, bool isConstant, _IOption<DAST._IExpression> defaultValue, bool isStatic) {
      parent.AddUnsupported("Datatype field " + item.dtor_name);
    }

    public object Finish() {
      parent.AddDatatype((Datatype)Datatype.create(
        Sequence<Rune>.UnicodeFromString(name),
        Sequence<Rune>.UnicodeFromString(docString),
        Sequence<Rune>.UnicodeFromString(enclosingModule),
        Sequence<DAST.TypeArgDecl>.FromArray(typeParams.ToArray()),
        Sequence<DAST.DatatypeCtor>.FromArray(ctors.ToArray()),
        Sequence<DAST.Method>.FromArray(body.ToArray()),
        isCo, attributes,
        Sequence<DAST.Type>.FromArray(superTraitTypes.ToArray())
      ));
      return parent;
    }
  }

  interface ClassLike {
    void AddMethod(DAST.Method item);

    void AddField(DAST.Formal item, bool isConstant, _IOption<DAST._IExpression> defaultValue, bool isStatic);

    public MethodBuilder Method(bool isStatic, bool hasBody, bool outVarsAreUninitFieldsToAssign, bool wasFunction,
      ISequence<ISequence<Rune>> overridingPath,
      string docString,
      ISequence<_IAttribute> attributes,
      string name,
      List<TypeArgDecl> typeArgs,
      Sequence<DAST.Formal> params_,
      List<DAST.Type> outTypes, List<ISequence<Rune>> outVars) {
      return new MethodBuilder(this, isStatic, hasBody, outVarsAreUninitFieldsToAssign, wasFunction, overridingPath, docString, attributes, name, typeArgs, params_, outTypes, outVars);
    }

    public object Finish();
  }

  class MethodBuilder(
    ClassLike parent,
    bool isStatic,
    bool hasBody,
    bool outVarsAreUninitFieldsToAssign,
    bool wasFunction,
    ISequence<ISequence<Rune>> overridingPath,
    string docString,
    ISequence<_IAttribute> attributes,
    string name,
    List<DAST.TypeArgDecl> typeArgs,
    Sequence<DAST.Formal> params_,
    List<DAST.Type> outTypes,
    List<ISequence<Rune>> outVars)
    : StatementContainer {
    readonly ClassLike parent = parent;
    readonly List<object> body = [];
    private ISequence<Rune> docString = Sequence<Rune>.UnicodeFromString(docString);

    public List<object> ForkList() {
      var ret = new List<object>();
      body.Add(ret);
      return ret;
    }

    public void AddStatement(DAST.Statement item) {
      body.Add(item);
    }

    public void AddBuildable(BuildableStatement item) {
      body.Add(item);
    }

    public DAST.Method Build() {
      List<DAST.Statement> builtStatements = [];
      StatementContainer.RecursivelyBuild(body, builtStatements);
      return (DAST.Method)DAST.Method.create(
        docString,
        attributes,
        isStatic,
        hasBody,
        outVarsAreUninitFieldsToAssign,
        wasFunction,
        overridingPath != null ? Option<ISequence<ISequence<Rune>>>.create_Some(overridingPath) : Option<ISequence<ISequence<Rune>>>.create_None(),
        Sequence<Rune>.UnicodeFromString(name),
        Sequence<DAST.TypeArgDecl>.FromArray(typeArgs.ToArray()),
        params_,
        Sequence<DAST.Statement>.FromArray(builtStatements.ToArray()),
        Sequence<DAST.Type>.FromArray(outTypes.ToArray()),
        outVars != null ? Option<ISequence<ISequence<Rune>>>.create_Some(Sequence<ISequence<Rune>>.FromArray(outVars.ToArray())) : Option<ISequence<ISequence<Rune>>>.create_None()
      );
    }

    public void AddUnsupported(string why) {
      AddStatement(StatementContainer.UnsupportedToStatement(why));
    }
  }

  interface StatementContainer : Container {
    void AddStatement(DAST.Statement item);

    void AddBuildable(BuildableStatement item);

    public static DAST.Statement UnsupportedToStatement(string why) {
      return (DAST.Statement)DAST.Statement.create_Print(ExprContainer.UnsupportedToExpr(why));
    }

    List<object> ForkList();

    public StatementContainer Fork() {
      return new ForkedStatementContainer(ForkList());
    }

    protected static void RecursivelyBuild(List<object> body, List<DAST.Statement> builtStatements) {
      foreach (var maybeBuilt in body) {
        if (maybeBuilt is DAST.Statement built) {
          builtStatements.Add(built);
        } else if (maybeBuilt is BuildableStatement buildable) {
          builtStatements.Add(buildable.Build());
        } else if (maybeBuilt is List<object> rec) {
          RecursivelyBuild(rec, builtStatements);
        } else {
          throw new InvalidOperationException("Unknown buildable type");
        }
      }
    }

    public void Print(DAST.Expression expr) {
      AddStatement((DAST.Statement)DAST.Statement.create_Print(expr));
    }

    public AssignBuilder Assign() {
      var ret = new AssignBuilder();
      AddBuildable(ret);
      return ret;
    }

    public DeclareBuilder DeclareAndAssign(DAST.Type type, string name) {
      var ret = new DeclareBuilder(type, name);
      AddBuildable(ret);
      return ret;
    }

    public IfElseBuilder IfElse() {
      var ret = new IfElseBuilder();
      AddBuildable(ret);
      return ret;
    }

    public WhileBuilder While() {
      var ret = new WhileBuilder();
      AddBuildable(ret);
      return ret;
    }

    public ForeachBuilder Foreach(string boundName, DAST.Type boundType) {
      var ret = new ForeachBuilder(boundName, boundType);
      AddBuildable(ret);
      return ret;
    }

    public TailRecursiveBuilder TailRecursive() {
      var ret = new TailRecursiveBuilder();
      AddBuildable(ret);
      return ret;
    }

    public CallStmtBuilder Call(ISequence<_IFormal> signature) {
      var ret = new CallStmtBuilder(signature);
      AddBuildable(ret);
      return ret;
    }

    public ReturnBuilder Return() {
      var ret = new ReturnBuilder();
      AddBuildable(ret);
      return ret;
    }

    public LabeledBuilder Labeled(string label) {
      var ret = new LabeledBuilder(label);
      AddBuildable(ret);
      return ret;
    }
  }

  interface BuildableStatement {
    DAST.Statement Build();
  }

  class ForkedStatementContainer(List<object> list) : StatementContainer {
    public void AddStatement(DAST.Statement item) {
      list.Add(item);
    }

    public void AddBuildable(BuildableStatement item) {
      list.Add(item);
    }

    public List<object> ForkList() {
      var ret = new List<object>();
      list.Add(ret);
      return ret;
    }

    public void AddUnsupported(string why) {
      AddStatement(StatementContainer.UnsupportedToStatement(why));
    }
  }

  class DeclareBuilder(DAST.Type type, string name) : ExprContainer, BuildableStatement {
    public object value;

    public void AddExpr(DAST.Expression value) {
      if (this.value != null) {
        throw new InvalidOperationException();
      } else {
        this.value = value;
      }
    }

    public void AddBuildable(BuildableExpr value) {
      if (this.value != null) {
        throw new InvalidOperationException();
      } else {
        this.value = value;
      }
    }

    public DAST.Statement Build() {
      if (this.value == null) {
        return (DAST.Statement)DAST.Statement.create_DeclareVar(
          Sequence<Rune>.UnicodeFromString(name), type, Option<DAST._IExpression>.create_None());
      } else {
        var builtValue = new List<DAST.Expression>();
        ExprContainer.RecursivelyBuild([value], builtValue);
        return (DAST.Statement)DAST.Statement.create_DeclareVar(Sequence<Rune>.UnicodeFromString(name), type, Option<DAST._IExpression>.create_Some(builtValue[0]));
      }
    }

    public void AddUnsupported(string why) {
      AddExpr(Compilers.ExprContainer.UnsupportedToExpr(why));
    }
  }

  class AssignBuilder : LhsContainer, ExprContainer, BuildableStatement {
    object lhs = null;
    public object value;

    public void AddLhs(DAST.AssignLhs lhs) {
      if (this.lhs != null && this.lhs != lhs) {
        throw new InvalidOperationException("Cannot change name of variable in assignment: " + this.lhs + " -> " + lhs);
      } else {
        this.lhs = lhs;
      }
    }

    public void AddBuildable(BuildableLhs lhs) {
      if (this.lhs != null && this.lhs != lhs) {
        throw new InvalidOperationException("Cannot change name of variable in assignment: " + this.lhs + " -> " + lhs);
      } else {
        this.lhs = lhs;
      }
    }

    public void AddExpr(DAST.Expression value) {
      if (this.value != null) {
        throw new InvalidOperationException();
      } else {
        this.value = value;
      }
    }

    public void AddBuildable(BuildableExpr value) {
      if (this.value != null) {
        throw new InvalidOperationException();
      } else {
        this.value = value;
      }
    }
    public void AddUnsupported(string why) {
      AddExpr(Compilers.ExprContainer.UnsupportedToExpr(why));
    }

    public DAST.Statement Build() {

      var builtLhs = LhsContainer.Build(lhs);
      DAST.Expression rhs;
      if (this.value == null) {
        rhs = ExprContainer.UnsupportedToExpr("<i>Cannot assign null value to variable</i>: " + lhs);
      } else {
        var builtValue = new List<DAST.Expression>();
        ExprContainer.RecursivelyBuild([value], builtValue);
        rhs = builtValue[0];
      }

      return (DAST.Statement)DAST.Statement.create_Assign(builtLhs, rhs);
    }
  }

  class IfElseBuilder : ExprContainer, StatementContainer, BuildableStatement {
    object condition = null;
    readonly List<object> ifBody = [];
    readonly List<object> elseBody = [];

    public object Condition => condition;

    public IfElseBuilder() { }

    public void AddExpr(DAST.Expression value) {
      if (condition != null) {
        throw new InvalidOperationException();
      } else {
        condition = value;
      }
    }

    public void AddBuildable(BuildableExpr value) {
      if (condition != null) {
        throw new InvalidOperationException();
      } else {
        condition = value;
      }
    }

    public void AddStatement(DAST.Statement item) {
      ifBody.Add(item);
    }

    public void AddBuildable(BuildableStatement item) {
      ifBody.Add(item);
    }

    public List<object> ForkList() {
      var ret = new List<object>();
      this.ifBody.Add(ret);
      return ret;
    }

    public void AddElseStatement(DAST.Statement item) {
      elseBody.Add(item);
    }

    public void AddElseBuildable(BuildableStatement item) {
      elseBody.Add(item);
    }

    public List<object> ElseForkList() {
      var ret = new List<object>();
      this.elseBody.Add(ret);
      return ret;
    }

    public ElseBuilder Else() {
      return new ElseBuilder(this);
    }

    public DAST.Statement Build() {
      List<DAST.Expression> builtCondition = [];
      ExprContainer.RecursivelyBuild(
        [condition ?? ExprContainer.UnsupportedToExpr("<i>condition to if expression</i>")], builtCondition);

      List<DAST.Statement> builtIfStatements = [];
      StatementContainer.RecursivelyBuild(ifBody, builtIfStatements);

      List<DAST.Statement> builtElseStatements = [];
      StatementContainer.RecursivelyBuild(elseBody, builtElseStatements);

      return (DAST.Statement)DAST.Statement.create_If(
        builtCondition[0],
        Sequence<DAST.Statement>.FromArray(builtIfStatements.ToArray()),
        Sequence<DAST.Statement>.FromArray(builtElseStatements.ToArray())
      );
    }

    public void AddUnsupported(string why) {
      condition = ExprContainer.UnsupportedToExpr(why);
    }
  }

  class ElseBuilder(IfElseBuilder parent) : StatementContainer {
    public readonly IfElseBuilder parent = parent;

    public List<object> ForkList() {
      return parent.ElseForkList();
    }

    public void AddStatement(DAST.Statement item) {
      parent.AddElseStatement(item);
    }

    public void AddBuildable(BuildableStatement item) {
      parent.AddElseBuildable(item);
    }

    public void AddUnsupported(string why) {
      AddStatement(StatementContainer.UnsupportedToStatement(why));
    }
  }

  class WhileBuilder : ExprContainer, StatementContainer, BuildableStatement {
    object condition = null;
    readonly List<object> body = [];
    public object Condition => condition;

    public void AddExpr(DAST.Expression value) {
      if (condition != null) {
        throw new InvalidOperationException();
      } else {
        condition = value;
      }
    }

    public void AddBuildable(BuildableExpr value) {
      if (condition != null) {
        throw new InvalidOperationException();
      } else {
        condition = value;
      }
    }

    public void AddStatement(DAST.Statement item) {
      body.Add(item);
    }

    public void AddBuildable(BuildableStatement item) {
      body.Add(item);
    }

    public List<object> ForkList() {
      var ret = new List<object>();
      this.body.Add(ret);
      return ret;
    }

    public DAST.Statement Build() {
      List<DAST.Expression> builtCondition = [];
      ExprContainer.RecursivelyBuild([condition], builtCondition);

      List<DAST.Statement> builtStatements = [];
      StatementContainer.RecursivelyBuild(body, builtStatements);

      return (DAST.Statement)DAST.Statement.create_While(
        builtCondition[0],
        Sequence<DAST.Statement>.FromArray(builtStatements.ToArray())
      );
    }

    public void AddUnsupported(string why) {
      AddStatement(StatementContainer.UnsupportedToStatement(why));
    }
  }

  class ForeachBuilder(string boundName, DAST.Type boundType) : ExprContainer, StatementContainer, BuildableStatement {
    object over = null;
    readonly List<object> body = [];

    public void AddExpr(DAST.Expression value) {
      if (over != null) {
        throw new InvalidOperationException();
      } else {
        over = value;
      }
    }

    public void AddBuildable(BuildableExpr value) {
      if (over != null) {
        throw new InvalidOperationException();
      } else {
        over = value;
      }
    }

    public void AddStatement(DAST.Statement item) {
      body.Add(item);
    }

    public void AddBuildable(BuildableStatement item) {
      body.Add(item);
    }

    public List<object> ForkList() {
      var ret = new List<object>();
      this.body.Add(ret);
      return ret;
    }

    public DAST.Statement Build() {
      List<DAST.Expression> builtOver = [];
      ExprContainer.RecursivelyBuild([over ?? ExprContainer.UnsupportedToExpr("<i>Foreach over is null</i>")], builtOver);

      List<DAST.Statement> builtStatements = [];
      StatementContainer.RecursivelyBuild(body, builtStatements);

      return (DAST.Statement)DAST.Statement.create_Foreach(
        Sequence<Rune>.UnicodeFromString(boundName),
        boundType,
        builtOver[0],
        Sequence<DAST.Statement>.FromArray(builtStatements.ToArray())
      );
    }

    public void AddUnsupported(string why) {
      AddStatement(StatementContainer.UnsupportedToStatement(why));
    }
  }

  class TailRecursiveBuilder : StatementContainer, BuildableStatement {
    readonly List<object> body = [];

    public TailRecursiveBuilder() { }

    public void AddStatement(DAST.Statement item) {
      body.Add(item);
    }

    public void AddBuildable(BuildableStatement item) {
      body.Add(item);
    }

    public List<object> ForkList() {
      var ret = new List<object>();
      this.body.Add(ret);
      return ret;
    }

    public DAST.Statement Build() {
      List<DAST.Statement> builtStatements = [];
      StatementContainer.RecursivelyBuild(body, builtStatements);

      return (DAST.Statement)DAST.Statement.create_TailRecursive(
        Sequence<DAST.Statement>.FromArray(builtStatements.ToArray())
      );
    }

    public void AddUnsupported(string why) {
      AddStatement(StatementContainer.UnsupportedToStatement(why));
    }
  }

  class CallStmtBuilder(ISequence<_IFormal> signature) : ExprContainer, BuildableStatement {
    object on = null;
    DAST.CallName name = null;
    List<DAST.Type> typeArgs = null;
    readonly List<object> args = [];
    List<ISequence<Rune>> outs = null;
    public readonly ISequence<_IFormal> Signature = signature;

    public void SetName(CallName name) {
      if (this.name != null) {
        throw new InvalidOperationException();
      } else {
        this.name = name;
      }
    }

    public void SetTypeArgs(List<DAST.Type> typeArgs) {
      if (this.typeArgs != null) {
        throw new InvalidOperationException();
      } else {
        this.typeArgs = typeArgs;
      }
    }

    public void AddExpr(DAST.Expression value) {
      if (on == null) {
        on = value;
      } else {
        args.Add(value);
      }
    }

    public void AddBuildable(BuildableExpr value) {
      if (on == null) {
        on = value;
      } else {
        args.Add(value);
      }
    }

    public void SetOuts(List<ISequence<Rune>> outs) {
      if (this.outs != null) {
        throw new InvalidOperationException();
      } else {
        this.outs = outs;
      }
    }

    public DAST.Statement Build() {
      List<DAST.Expression> builtOn = [];
      ExprContainer.RecursivelyBuild([on], builtOn);

      List<DAST.Expression> builtArgs = [];
      ExprContainer.RecursivelyBuild(args, builtArgs);

      return (DAST.Statement)DAST.Statement.create_Call(
        builtOn[0],
        name,
        Sequence<DAST.Type>.FromArray(typeArgs.ToArray()),
        Sequence<DAST.Expression>.FromArray(builtArgs.ToArray()),
        outs == null ? Option<ISequence<ISequence<Rune>>>.create_None() : Option<ISequence<ISequence<Rune>>>.create_Some(Sequence<ISequence<Rune>>.FromArray(outs.ToArray()))
      );
    }

    public void AddUnsupported(string why) {
      AddExpr(ExprContainer.UnsupportedToExpr(why));
    }
  }

  class ReturnBuilder : ExprContainer, BuildableStatement {
    object value = null;

    public ReturnBuilder() { }

    public void AddExpr(DAST.Expression value) {
      if (this.value != null) {
        throw new InvalidOperationException();
      } else {
        this.value = value;
      }
    }

    public void AddBuildable(BuildableExpr value) {
      if (this.value != null) {
        AddUnsupported("Second value for ReturnBuilder");
      } else {
        this.value = value;
      }
    }

    public DAST.Statement Build() {
      var builtValue = new List<DAST.Expression>();
      if (value == null) {
        return (DAST.Statement)DAST.Statement.create_EarlyReturn();
      }
      ExprContainer.RecursivelyBuild([value], builtValue);

      return (DAST.Statement)DAST.Statement.create_Return(builtValue[0]);
    }

    public void AddUnsupported(string why) {
      value = ExprContainer.UnsupportedToExpr(why);
    }
  }

  class LabeledBuilder(string label) : BuildableStatement, StatementContainer {
    readonly List<object> statements = [];

    public void AddStatement(DAST.Statement item) {
      statements.Add(item);
    }

    public void AddBuildable(BuildableStatement item) {
      statements.Add(item);
    }

    public StatementContainer Fork() {
      return new ForkedStatementContainer(ForkList());
    }

    public List<object> ForkList() {
      var ret = new List<object>();
      statements.Add(ret);
      return ret;
    }

    public DAST.Statement Build() {
      List<DAST.Statement> builtStatements = [];
      StatementContainer.RecursivelyBuild(statements, builtStatements);

      return (DAST.Statement)DAST.Statement.create_Labeled(
        Sequence<Rune>.UnicodeFromString(label),
        Sequence<DAST.Statement>.FromArray(builtStatements.ToArray())
      );
    }

    public void AddUnsupported(string why) {
      AddStatement(StatementContainer.UnsupportedToStatement(why));
    }
  }

  class NoStatementBuffer : StatementContainer {
    public void AddUnsupported(string why) {
      throw new Exception(why);
    }

    public void AddStatement(DAST.Statement item) {
      throw new Exception("<i>Add statements in pure expressions</i>, in a context where statements can't be added, tried to add " + item);
    }

    public void AddBuildable(BuildableStatement item) {
      throw new Exception("<i>Add buildable statements in pure expressions</i>, in a context where statements can't be added, tried to add " + item);
    }

    public List<object> ForkList() {
      throw new Exception("<i>Fork statements in pure expressions</i>, in a context where statements can't be added");
    }
  }

  class StatementBuffer : StatementContainer {
    readonly List<object> statements = [];

    public void AddStatement(DAST.Statement item) {
      statements.Add(item);
    }

    public void AddBuildable(BuildableStatement item) {
      statements.Add(item);
    }

    public List<object> ForkList() {
      var ret = new List<object>();
      statements.Add(ret);
      return ret;
    }

    public List<DAST.Statement> PopAll() {
      var builtResult = new List<DAST.Statement>();
      StatementContainer.RecursivelyBuild(statements, builtResult);

      return builtResult;
    }

    public void AddUnsupported(string why) {
      AddStatement(StatementContainer.UnsupportedToStatement(why));
    }
  }

  class ExprWrapper(Func<DAST.Expression, DAST.Expression> internalWrapper = null)
    : ExprContainer, BuildableExpr {
    public Func<DAST.Expression, DAST.Expression> InternalWrapper = internalWrapper;
    [CanBeNull] public object Expr;

    public void AddExpr(DAST.Expression item) {
      if (Expr == null) {
        Expr = item;
      } else {
        throw new InvalidOperationException("AddExpr already had an object");
      }
    }

    public void AddBuildable(BuildableExpr item) {
      if (Expr == null) {
        Expr = item;
      } else {
        throw new InvalidOperationException("AddExpr already had an object");
      }
    }

    public DAST.Expression Finish() {
      if (Expr == null) {
        return ExprContainer.UnsupportedToExpr("Expected exactly one expression for ExprWrapper, got none");
      } else if (Expr is BuildableExpr b) {
        return b.Build();
      } else if (Expr is DAST.Expression e) {
        return e;
      } else {
        return ExprContainer.UnsupportedToExpr("Expected exactly one expression for ExprWrapper, got " + Expr);
      }
    }

    public void AddUnsupported(string why) {
      AddExpr(ExprContainer.UnsupportedToExpr(why));
    }

    public DAST.Expression Build() {
      if (InternalWrapper == null) {
        return Finish();
      } else {
        return InternalWrapper(Finish());
      }
    }
  }

  class ExprBuffer(object returnTo) : ExprContainer, BuildableExpr {
    Stack<object> exprs = new();
    public readonly object parent = returnTo;

    public void AddExpr(DAST.Expression item) {
      exprs.Push(item);
    }

    public void AddBuildable(BuildableExpr item) {
      exprs.Push(item);
    }

    public List<DAST.Expression> PopN(int n) {
      if (exprs.Count < n) {
        throw new InvalidOperationException();
      } else {
        var result = new List<object>();
        for (int i = 0; i < n; i++) {
          result.Insert(0, exprs.Pop());
        }

        var builtResult = new List<DAST.Expression>();
        ExprContainer.RecursivelyBuild(result, builtResult);

        return builtResult;
      }
    }

    public List<DAST.Expression> PopAll() {
      return PopN(exprs.Count);
    }

    public DAST.Expression Finish() {
      if (exprs.Count != 1) {
        return ExprContainer.UnsupportedToExpr("Expected exactly one expression in buffer, got " +
                                               exprs.Comma(e => e.ToString()));
      } else {
        return PopN(1)[0];
      }
    }

    public void AddUnsupported(string why) {
      AddExpr(ExprContainer.UnsupportedToExpr(why));
    }

    public DAST.Expression Build() {
      return Finish();
    }
  }

  interface ExprContainer : Container {
    void AddExpr(DAST.Expression item);

    void AddBuildable(BuildableExpr item);

    ExprWrapper Wrapper(Func<DAST.Expression, DAST.Expression> wrapper) {
      var ret = new ExprWrapper(wrapper);
      AddBuildable(ret);
      return ret;
    }

    BinOpBuilder BinOp(DAST.BinOp op, DAST.Type leftType, DAST.Type rightType, DAST.Type resType) {
      var ret = new BinOpBuilder(op, leftType, rightType, resType);
      AddBuildable(ret);
      return ret;
    }

    BinOpBuilder BinOp(string op, Func<DAST.Expression, DAST.Expression, DAST.Expression> callback) {
      var ret = new BinOpBuilder(op, callback);
      AddBuildable(ret);
      return ret;
    }

    CallExprBuilder Call(ISequence<_IFormal> signature) {
      var ret = new CallExprBuilder(signature);
      AddBuildable(ret);
      return ret;
    }

    ApplyExprBuilder Apply() {
      var ret = new ApplyExprBuilder();
      AddBuildable(ret);
      return ret;
    }

    LambdaExprBuilder Lambda(List<DAST.Formal> formals, DAST.Type retType) {
      var ret = new LambdaExprBuilder(formals, retType);
      AddBuildable(ret);
      return ret;
    }

    IIFEExprBuilder IIFE(string name, DAST.Type tpe) {
      var ret = new IIFEExprBuilder(name, tpe);
      AddBuildable(ret);
      return ret;
    }

    BetaRedexBuilder BetaRedex(List<_System.Tuple2<DAST.Formal, DAST.Expression>> bindings, DAST.Type retType) {
      var ret = new BetaRedexBuilder(bindings, retType);
      AddBuildable(ret);
      return ret;
    }

    ConvertBuilder Convert(DAST.Type fromType, DAST.Type toType) {
      var ret = new ConvertBuilder(fromType, toType);
      AddBuildable(ret);
      return ret;
    }

    IndexBuilder Index(List<DAST.Expression> indices, DAST._ICollKind collKind) {
      var ret = new IndexBuilder(indices, collKind);
      AddBuildable(ret);
      return ret;
    }

    protected static void RecursivelyBuild(List<object> body, List<DAST.Expression> builtExprs) {
      foreach (var maybeBuilt in body) {
        if (maybeBuilt is DAST.Expression built) {
          builtExprs.Add(built);
        } else if (maybeBuilt is BuildableExpr buildable) {
          builtExprs.Add(buildable.Build());
        } else {
          throw new InvalidOperationException(
            "Unknown buildable type: " +
            (maybeBuilt == null ? "NULL" :
             maybeBuilt.GetType())
            );
        }
      }
    }

    static DAST.Expression UnsupportedToExpr(string why) {
      return (DAST.Expression)DAST.Expression.create_Ident(
        Sequence<ISequence<Rune>>.UnicodeFromString($"uncompilable(\"<i>Unsupported: {why}</i>\")")
      );
    }
  }

  interface LhsContainer : Container {
    void AddLhs(DAST.AssignLhs lhs);

    void AddBuildable(BuildableLhs lhs);

    ArrayLhs Array(List<DAST.Expression> indices) {
      var ret = new ArrayLhs(indices);
      AddBuildable(ret);
      return ret;
    }

    protected static DAST.AssignLhs Build(object maybeBuilt) {
      if (maybeBuilt is DAST.AssignLhs built) {
        return built;
      } else if (maybeBuilt is BuildableLhs buildable) {
        return buildable.Build();
      } else {
        throw new InvalidOperationException("Unknown buildable type: " + maybeBuilt.GetType());
      }
    }
  }

  interface BuildableLhs {
    DAST.AssignLhs Build();
  }

  class ArrayLhs(List<DAST.Expression> indices) : BuildableLhs, ExprContainer {
    object arrayExpr = null;
    readonly System.Diagnostics.StackTrace stackTrace = new(true);

    public void AddExpr(DAST.Expression item) {
      if (arrayExpr != null) {
        throw new InvalidOperationException();
      } else {
        arrayExpr = item;
      }
    }

    public void AddBuildable(BuildableExpr item) {
      if (arrayExpr != null) {
        throw new InvalidOperationException();
      } else {
        arrayExpr = item;
      }
    }

    public DAST.AssignLhs Build() {
      if (arrayExpr == null) {
        Console.WriteLine(stackTrace);
      }
      var builtArrayExpr = new List<DAST.Expression>();
      ExprContainer.RecursivelyBuild([arrayExpr], builtArrayExpr);

      return (DAST.AssignLhs)DAST.AssignLhs.create_Index(builtArrayExpr[0], Sequence<DAST.Expression>.FromArray(indices.ToArray()));
    }

    public void AddUnsupported(string why) {
      arrayExpr = ExprContainer.UnsupportedToExpr(why);
    }
  }

  interface BuildableExpr {
    DAST.Expression Build();
  }

  class BinOpBuilder : ExprContainer, BuildableExpr {
    private readonly Func<DAST.Expression, DAST.Expression, DAST.Expression> internalBuilder;
    readonly List<object> operands = [];
    private readonly string op;

    public BinOpBuilder(DAST.BinOp op, DAST.Type leftType, DAST.Type rightType, DAST.Type resType) {
      this.internalBuilder = (DAST.Expression left, DAST.Expression right) =>
        (DAST.Expression)DAST.Expression.create_BinOp(
          DAST.TypedBinOp.create_TypedBinOp(op, leftType, rightType, resType), left, right, new BinaryOpFormat_NoFormat());
      this.op = op.ToString();
    }

    public BinOpBuilder(string op, Func<DAST.Expression, DAST.Expression, DAST.Expression> callback) {
      this.op = op;
      internalBuilder = callback;
    }

    public void AddExpr(DAST.Expression item) {
      operands.Add(item);
    }

    public void AddBuildable(BuildableExpr item) {
      operands.Add(item);
    }

    public DAST.Expression Build() {
      var builtOperands = new List<DAST.Expression>();
      ExprContainer.RecursivelyBuild(operands, builtOperands);

      if (operands.Count != 2) {
        builtOperands.Insert(0, ExprContainer.UnsupportedToExpr(op + " with not 2 elements"));
        return (DAST.Expression)DAST.Expression.create_SetValue(
          Sequence<DAST.Expression>.FromElements(builtOperands.ToArray()));
      }

      return internalBuilder(builtOperands[0], builtOperands[1]);
    }

    public void AddUnsupported(string why) {
      AddExpr(ExprContainer.UnsupportedToExpr(why));
    }
  }

  class CallExprBuilder(ISequence<_IFormal> signature) : ExprContainer, BuildableExpr {
    object on = null;
    DAST.CallName name = null;
    List<DAST.Type> typeArgs = null;
    readonly List<object> args = [];
    List<ISequence<Rune>> outs = null;

    public ISequence<_IFormal> Signature { get; } = signature;

    public void SetName(DAST.CallName name) {
      if (this.name != null) {
        throw new InvalidOperationException();
      } else {
        this.name = name;
      }
    }

    public void SetTypeArgs(List<DAST.Type> typeArgs) {
      if (this.typeArgs != null) {
        throw new InvalidOperationException();
      } else {
        this.typeArgs = typeArgs;
      }
    }

    public void AddExpr(DAST.Expression value) {
      if (on == null) {
        on = value;
      } else {
        args.Add(value);
      }
    }

    public void AddBuildable(BuildableExpr value) {
      if (on == null) {
        on = value;
      } else {
        args.Add(value);
      }
    }

    public void SetOuts(List<ISequence<Rune>> outs) {
      if (this.outs != null) {
        throw new InvalidOperationException();
      } else {
        this.outs = outs;
      }
    }

    public DAST.Expression Build() {
      var builtOn = new List<DAST.Expression>();
      ExprContainer.RecursivelyBuild([on], builtOn);

      var builtArgs = new List<DAST.Expression>();
      ExprContainer.RecursivelyBuild(args, builtArgs);

      return (DAST.Expression)DAST.Expression.create_Call(
        builtOn[0],
        name,
        Sequence<DAST.Type>.FromArray((typeArgs ?? []).ToArray()),
        Sequence<DAST.Expression>.FromArray(builtArgs.ToArray())
      );
    }

    public void AddUnsupported(string why) {
      AddExpr(ExprContainer.UnsupportedToExpr(why));
    }
  }

  class ApplyExprBuilder : ExprContainer, BuildableExpr {
    object on = null;
    readonly List<object> args = [];

    public ApplyExprBuilder() { }

    public void AddExpr(DAST.Expression value) {
      if (on == null) {
        on = value;
      } else {
        args.Add(value);
      }
    }

    public void AddBuildable(BuildableExpr value) {
      if (on == null) {
        on = value;
      } else {
        args.Add(value);
      }
    }

    public DAST.Expression Build() {
      var builtOn = new List<DAST.Expression>();
      ExprContainer.RecursivelyBuild([on], builtOn);

      var builtArgs = new List<DAST.Expression>();
      ExprContainer.RecursivelyBuild(args, builtArgs);

      return (DAST.Expression)DAST.Expression.create_Apply(
        builtOn[0],
        Sequence<DAST.Expression>.FromArray(builtArgs.ToArray())
      );
    }

    public void AddUnsupported(string why) {
      AddExpr(ExprContainer.UnsupportedToExpr(why));
    }
  }

  class LambdaExprBuilder(List<DAST.Formal> formals, DAST.Type retType) : StatementContainer, BuildableExpr {
    readonly List<object> body = [];

    public void AddStatement(DAST.Statement item) {
      body.Add(item);
    }

    public void AddBuildable(BuildableStatement item) {
      body.Add(item);
    }

    public List<object> ForkList() {
      var ret = new List<object>();
      body.Add(ret);
      return ret;
    }

    public DAST.Expression Build() {
      var builtBody = new List<DAST.Statement>();
      StatementContainer.RecursivelyBuild(body, builtBody);

      return (DAST.Expression)DAST.Expression.create_Lambda(
        Sequence<DAST.Formal>.FromArray(formals.ToArray()),
        retType,
        Sequence<DAST.Statement>.FromArray(builtBody.ToArray())
      );
    }

    public void AddUnsupported(string why) {
      AddStatement(StatementContainer.UnsupportedToStatement(why));
    }
  }

  class IIFEExprBuilder(string name, DAST.Type tpe) : ExprContainer, BuildableExpr {
    object body = null;
    public object value = null;

    public IIFEExprRhs RhsBuilder() {
      return new IIFEExprRhs(this);
    }

    public void AddExpr(DAST.Expression item) {
      if (body != null) {
        throw new InvalidOperationException();
      } else {
        body = item;
      }
    }

    public void AddBuildable(BuildableExpr item) {
      if (body != null) {
        throw new InvalidOperationException();
      } else {
        body = item;
      }
    }

    public DAST.Expression Build() {
      var builtBody = new List<DAST.Expression>();
      ExprContainer.RecursivelyBuild([body ?? ExprContainer.UnsupportedToExpr("IIFEExprBuilder with empty body")], builtBody);

      var builtValue = new List<DAST.Expression>();
      ExprContainer.RecursivelyBuild([
        value
        ?? ExprContainer.UnsupportedToExpr("IIFEExprBuilder with empty value")
      ], builtValue);

      return (DAST.Expression)DAST.Expression.create_IIFE(
        Sequence<Rune>.UnicodeFromString(name),
        tpe,
        builtValue[0],
        builtBody[0]
      );
    }

    public void AddUnsupported(string why) {
      AddExpr(ExprContainer.UnsupportedToExpr(why));
    }
  }

  class IIFEExprRhs(IIFEExprBuilder parent) : ExprContainer {
    public void AddExpr(DAST.Expression item) {
      if (parent.value != null) {
        throw new InvalidOperationException();
      } else {
        parent.value = item;
      }
    }

    public void AddBuildable(BuildableExpr item) {
      if (parent.value != null) {
        throw new InvalidOperationException();
      } else {
        parent.value = item;
      }
    }

    public void AddUnsupported(string why) {
      AddExpr(ExprContainer.UnsupportedToExpr(why));
    }
  }

  class BetaRedexBuilder(List<_System.Tuple2<DAST.Formal, DAST.Expression>> bindings, DAST.Type retType)
    : ExprContainer, BuildableExpr {
    object body = null;

    public void AddExpr(DAST.Expression item) {
      body = item;
    }

    public void AddBuildable(BuildableExpr item) {
      body = item;
    }

    public DAST.Expression Build() {
      var builtBody = new List<DAST.Expression>();
      ExprContainer.RecursivelyBuild([body], builtBody);

      return (DAST.Expression)DAST.Expression.create_BetaRedex(
        Sequence<_System.Tuple2<DAST.Formal, DAST.Expression>>.FromArray(bindings.ToArray()),
        retType,
        builtBody[0]
      );
    }

    public void AddUnsupported(string why) {
      AddExpr(ExprContainer.UnsupportedToExpr(why));
    }
  }

  class ConvertBuilder(DAST.Type fromType, DAST.Type toType) : ExprContainer, BuildableExpr {
    object value = null;

    public void AddExpr(DAST.Expression item) {
      if (value != null) {
        throw new InvalidOperationException();
      } else {
        value = item;
      }
    }

    public void AddBuildable(BuildableExpr item) {
      if (value != null) {
        throw new InvalidOperationException();
      } else {
        value = item;
      }
    }

    public DAST.Expression Build() {
      var builtValue = new List<DAST.Expression>();
      DAST.Expression v;
      if (value == null) {
        v = ExprContainer.UnsupportedToExpr($"Conversion from {fromType} to {toType} of something missing");
      } else {
        ExprContainer.RecursivelyBuild([value], builtValue);
        v = builtValue[0];
      }

      return (DAST.Expression)DAST.Expression.create_Convert(
        v,
        fromType,
        toType
      );
    }

    public void AddUnsupported(string why) {
      AddExpr(ExprContainer.UnsupportedToExpr(why));
    }
  }

  class IndexBuilder(List<DAST.Expression> indices, DAST._ICollKind collKind) : ExprContainer, BuildableExpr {
    object value = null;

    public void AddExpr(DAST.Expression item) {
      if (value != null) {
        throw new InvalidOperationException();
      } else {
        value = item;
      }
    }

    public void AddBuildable(BuildableExpr item) {
      if (value != null) {
        throw new InvalidOperationException();
      } else {
        value = item;
      }
    }

    public DAST.Expression Build() {
      var builtValue = new List<DAST.Expression>();
      ExprContainer.RecursivelyBuild([value], builtValue);

      return (DAST.Expression)DAST.Expression.create_Index(
        builtValue[0],
        collKind,
        Sequence<DAST.Expression>.FromArray(indices.ToArray())
      );
    }

    public void AddUnsupported(string why) {
      AddExpr(ExprContainer.UnsupportedToExpr(why));
    }
  }

  class NativeRangeBuilder(string start = null) : ExprContainer, BuildableExpr {
    [CanBeNull] readonly string start = start;
    [CanBeNull] object bound = null;

    public void AddExpr(DAST.Expression item) {
      if (bound != null) {
        throw new InvalidOperationException();
      } else {
        bound = item;
      }
    }

    public void AddBuildable(BuildableExpr item) {
      if (bound != null) {
        throw new InvalidOperationException();
      } else {
        bound = item;
      }
    }

    public static DAST.Expression ToNativeUsize(int number) {
      var origType = DAST.Type.create_Primitive(DAST.Primitive.create_Int());
      var numberExpr = (DAST.Expression)DAST.Expression.create_Literal(
        DAST.Literal.create_IntLiteral(Sequence<Rune>.UnicodeFromString($"{number}"),
          origType)
      );
      return (DAST.Expression)DAST.Expression.create_Convert(numberExpr, origType, DAST.Type.create_UserDefined(
        DAST.ResolvedType.create_ResolvedType(
        Sequence<Sequence<Rune>>.FromElements((Sequence<Rune>)Sequence<Rune>.UnicodeFromString("usize")),
        Sequence<_IType>.Empty,
        DAST.ResolvedTypeBase.create_Newtype(origType, DAST.NewtypeRange.create_NativeArrayIndex(), true), Sequence<_IAttribute>.Empty,
        Sequence<Sequence<Rune>>.Empty, Sequence<_IType>.Empty)
      ));
    }

    public DAST.Expression Build() {
      var builtValue = new List<DAST.Expression>();
      DAST.Expression endExpr;
      if (bound == null) {
        endExpr = ExprContainer.UnsupportedToExpr($"NativeRangeBuilder has no upper bound");
      } else {
        ExprContainer.RecursivelyBuild([bound], builtValue);
        endExpr = builtValue[0];
      }

      DAST.Expression startExpr;
      if (start == null) {
        startExpr = ToNativeUsize(0);
      } else {
        startExpr = (DAST.Expression)DAST.Expression.create_Ident(
          Sequence<Rune>.UnicodeFromString(start));
      }

      return (DAST.Expression)DAST.Expression.create_IntRange(
        DAST.Type.create_Primitive(DAST.Primitive.create_Native()),
        startExpr, endExpr, true);
    }

    public void AddUnsupported(string why) {
      AddExpr(ExprContainer.UnsupportedToExpr(why));
    }
  }

  class ArrayLengthBuilder(DAST.Type arrayType, int dim, bool native) : ExprContainer, BuildableExpr {
    private object array = null;

    public void AddExpr(DAST.Expression item) {
      if (array != null) {
        throw new InvalidOperationException();
      } else {
        array = item;
      }
    }

    public void AddBuildable(BuildableExpr item) {
      if (array != null) {
        throw new InvalidOperationException();
      } else {
        array = item;
      }
    }

    public DAST.Expression Build() {
      var builtValue = new List<DAST.Expression>();
      DAST.Expression arrayExpr;
      if (array == null) {
        arrayExpr = ExprContainer.UnsupportedToExpr($"ArrayLengthBuilder has no array");
      } else {
        ExprContainer.RecursivelyBuild([array], builtValue);
        arrayExpr = builtValue[0];
      }

      return (DAST.Expression)DAST.Expression.create_ArrayLen(
        arrayExpr, arrayType, new BigInteger(dim), native);
    }

    public void AddUnsupported(string why) {
      AddExpr(ExprContainer.UnsupportedToExpr(why));
    }
  }
}
