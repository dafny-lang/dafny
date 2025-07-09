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

  class ModuleBuilder : ClassContainer, TraitContainer, NewtypeContainer, DatatypeContainer, SynonymTypeContainer {
    readonly ModuleContainer parent;
    readonly string name;
    readonly Sequence<Attribute> attributes;
    readonly List<ModuleItem> body = [];
    private readonly bool requiresExterns;
    private string docString;

    public ModuleBuilder(ModuleContainer parent, string name, string docString, Sequence<Attribute> attributes, bool requiresExterns) {
      this.parent = parent;
      this.name = name;
      this.attributes = attributes;
      this.requiresExterns = requiresExterns;
      this.docString = docString;
    }

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
        Sequence<Rune>.UnicodeFromString(this.name),
        Sequence<Rune>.UnicodeFromString(this.docString),
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



  class ClassBuilder : ClassLike {
    readonly ClassContainer parent;
    readonly string name;
    readonly string enclosingModule;
    readonly List<DAST.TypeArgDecl> typeParams;
    readonly List<DAST.Type> superClasses;
    readonly List<DAST.Field> fields = [];
    readonly List<DAST.Method> body = [];
    readonly ISequence<_IAttribute> attributes;
    private string docString;

    public ClassBuilder(ClassContainer parent, string name, string docString, string enclosingModule, List<DAST.TypeArgDecl> typeParams, List<DAST.Type> superClasses, ISequence<_IAttribute> attributes) {
      this.parent = parent;
      this.name = name;
      this.enclosingModule = enclosingModule;
      this.typeParams = typeParams;
      this.superClasses = superClasses;
      this.attributes = attributes;
      this.docString = docString;
    }

    public void AddMethod(DAST.Method item) {
      body.Add(item);
    }

    public void AddField(DAST.Formal item, bool isConstant, _IOption<DAST._IExpression> defaultValue, bool isStatic) {
      fields.Add((DAST.Field)DAST.Field.create_Field(item, isConstant, defaultValue, isStatic));
    }

    public object Finish() {
      parent.AddClass((Class)Class.create(
        Sequence<Rune>.UnicodeFromString(this.name),
        Sequence<Rune>.UnicodeFromString(this.docString),
        Sequence<Rune>.UnicodeFromString(this.enclosingModule),
        Sequence<DAST.TypeArgDecl>.FromArray(this.typeParams.ToArray()),
        Sequence<DAST.Type>.FromArray(this.superClasses.ToArray()),
        Sequence<DAST.Field>.FromArray(this.fields.ToArray()),
        Sequence<DAST.Method>.FromArray(body.ToArray()),
        attributes
      ));
      return parent;
    }
  }

  interface TraitContainer : Container {
    void AddTrait(Trait item);

    public TraitBuilder Trait(string name, List<TypeArgDecl> typeParams, List<DAST.Type> parents,
      ISequence<_IAttribute> attributes, string docString, _ITraitType traitType, List<DAST.Type> downcastableTraits) {
      return new TraitBuilder(this, name, docString, typeParams, parents, attributes, traitType, downcastableTraits);
    }
  }

  class TraitBuilder : ClassLike {
    readonly TraitContainer parent;
    readonly string name;
    readonly List<DAST.TypeArgDecl> typeParams;
    private readonly List<DAST.Type> parents;
    readonly List<DAST.Method> body = [];
    private ISequence<_IAttribute> attributes;
    private readonly string docString;
    private readonly _ITraitType traitType;
    private readonly List<DAST.Type> downcastableTraits;

    public TraitBuilder(TraitContainer parent, string name, string docString, List<DAST.TypeArgDecl> typeParams, List<DAST.Type> parents, ISequence<_IAttribute> attributes, _ITraitType traitType, List<DAST.Type> downcastableTraits) {
      this.parent = parent;
      this.name = name;
      this.typeParams = typeParams;
      this.attributes = attributes;
      this.docString = docString;
      this.traitType = traitType;
      this.downcastableTraits = downcastableTraits;
      this.parents = parents;
    }

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
      this.parent.AddUnsupported("var/const fro trait - " + item.dtor_name);
    }

    public object Finish() {
      parent.AddTrait((Trait)Trait.create(
        Sequence<Rune>.UnicodeFromString(this.name),
        Sequence<Rune>.UnicodeFromString(this.docString),
        Sequence<DAST.TypeArgDecl>.FromArray(typeParams.ToArray()),
        traitType,
        Sequence<DAST.Type>.FromArray(parents.ToArray()),
        Sequence<DAST.Type>.FromArray(downcastableTraits.ToArray()),
        Sequence<DAST.Method>.FromArray(body.ToArray()),
        attributes)
      );
      return parent;
    }
  }

  interface NewtypeContainer : Container {
    void AddNewtype(Newtype item);

    public NewtypeBuilder Newtype(string name, List<TypeArgDecl> typeParams,
      DAST.Type baseType, NewtypeRange newtypeRange, Option<NewtypeConstraint> constraint,
      List<DAST.Statement> witnessStmts, DAST.Expression witness,
      ISequence<_IAttribute> attributes, string docString, _IEqualitySupport equalitySupport) {
      return new NewtypeBuilder(this, name, typeParams, newtypeRange, baseType, constraint, witnessStmts, witness, attributes, docString, equalitySupport);
    }
  }

  class NewtypeBuilder : ClassLike {
    readonly NewtypeContainer parent;
    readonly string name;
    readonly List<DAST.TypeArgDecl> typeParams;
    readonly DAST.Type baseType;
    private readonly Option<DAST.NewtypeConstraint> constraint;
    private readonly DAST.NewtypeRange newtypeRange;
    readonly List<DAST.Statement> witnessStmts;
    readonly DAST.Expression witness;
    private ISequence<_IAttribute> attributes;
    private readonly List<DAST._IMethod> methods;
    private string docString;
    private _IEqualitySupport equalitySupport;

    public NewtypeBuilder(NewtypeContainer parent, string name, List<TypeArgDecl> typeParams,
      NewtypeRange newtypeRange, DAST.Type baseType, Option<DAST.NewtypeConstraint> constraint, List<DAST.Statement> statements,
      DAST.Expression witness,
      ISequence<_IAttribute> attributes, string docString, _IEqualitySupport equalitySupport) {
      this.parent = parent;
      this.name = name;
      this.typeParams = typeParams;
      this.newtypeRange = newtypeRange;
      this.baseType = baseType;
      this.constraint = constraint;
      this.witnessStmts = statements;
      this.witness = witness;
      this.attributes = attributes;
      this.docString = docString;
      this.equalitySupport = equalitySupport;
      this.methods = [];
    }

    public void AddMethod(DAST.Method item) {
      methods.Add(item);
    }

    public void AddField(DAST.Formal item, bool isConstant, _IOption<DAST._IExpression> defaultValue, bool isStatic) {
      parent.AddUnsupported("Newtype field " + item.dtor_name);
    }

    public object Finish() {
      parent.AddNewtype((Newtype)Newtype.create(
        Sequence<Rune>.UnicodeFromString(this.name),
        Sequence<Rune>.UnicodeFromString(this.docString),
        Sequence<DAST.TypeArgDecl>.FromArray(this.typeParams.ToArray()),
        this.baseType,
        newtypeRange,
        constraint,
        Sequence<DAST.Statement>.FromArray(this.witnessStmts.ToArray()),
        this.witness == null
          ? Option<DAST._IExpression>.create_None()
          : Option<DAST._IExpression>.create_Some(this.witness),
        equalitySupport,
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

  class SynonymTypeBuilder {
    readonly SynonymTypeContainer parent;
    readonly string name;
    readonly List<DAST.TypeArgDecl> typeParams;
    readonly DAST.Type rhsType;
    readonly List<DAST.Statement> witnessStmts;
    readonly DAST.Expression witness;
    private ISequence<_IAttribute> attributes;
    private string docString;

    public SynonymTypeBuilder(SynonymTypeContainer parent, string name, List<DAST.TypeArgDecl> typeParams,
      DAST.Type rhsType, List<DAST.Statement> statements, DAST.Expression witness,
      ISequence<_IAttribute> attributes, string docString) {
      this.parent = parent;
      this.name = name;
      this.typeParams = typeParams;
      this.rhsType = rhsType;
      this.witnessStmts = statements;
      this.witness = witness;
      this.attributes = attributes;
      this.docString = docString;
    }

    public object Finish() {
      parent.AddSynonymType((SynonymType)SynonymType.create(
        Sequence<Rune>.UnicodeFromString(this.name),
        Sequence<Rune>.UnicodeFromString(this.docString),
        Sequence<DAST.TypeArgDecl>.FromArray(this.typeParams.ToArray()),
        this.rhsType,
        Sequence<DAST.Statement>.FromArray(this.witnessStmts.ToArray()),
        this.witness == null
          ? Option<DAST._IExpression>.create_None()
          : Option<DAST._IExpression>.create_Some(this.witness),
        attributes
      ));
      return parent;
    }
  }

  interface DatatypeContainer : Container {
    void AddDatatype(Datatype item);

    public DatatypeBuilder Datatype(string name, string enclosingModule, List<TypeArgDecl> typeParams,
      List<DAST.DatatypeCtor> ctors, bool isCo, ISequence<_IAttribute> attributes, string docString,
      List<DAST.Type> superTraitTypes, List<DAST.Type> superNegativeTraitTypes, _IEqualitySupport equalitySupport) {
      return new DatatypeBuilder(this, name, docString, enclosingModule, typeParams, ctors, isCo, attributes, superTraitTypes, superNegativeTraitTypes, equalitySupport);
    }
  }

  class DatatypeBuilder : ClassLike {
    readonly DatatypeContainer parent;
    readonly string name;
    readonly string enclosingModule;
    readonly List<DAST.TypeArgDecl> typeParams;
    readonly List<DAST.DatatypeCtor> ctors;
    readonly bool isCo;
    readonly List<DAST.Method> body = [];
    readonly ISequence<_IAttribute> attributes;
    readonly string docString;
    readonly List<DAST.Type> superTraitTypes;
    readonly List<DAST.Type> superNegativeTraitTypes;
    private _IEqualitySupport equalitySupport;

    public DatatypeBuilder(DatatypeContainer parent, string name, string docString, string enclosingModule, List<DAST.TypeArgDecl> typeParams, List<DAST.DatatypeCtor> ctors, bool isCo, ISequence<_IAttribute> attributes, List<DAST.Type> superTraitTypes, List<DAST.Type> superNegativeTraitTypes, _IEqualitySupport equalitySupport) {
      this.parent = parent;
      this.name = name;
      this.docString = docString;
      this.typeParams = typeParams;
      this.enclosingModule = enclosingModule;
      this.ctors = ctors;
      this.isCo = isCo;
      this.attributes = attributes;
      this.superTraitTypes = superTraitTypes;
      this.superNegativeTraitTypes = superNegativeTraitTypes;
      this.equalitySupport = equalitySupport;
    }

    public void AddMethod(DAST.Method item) {
      body.Add(item);
    }

    public void AddField(DAST.Formal item, bool isConstant, _IOption<DAST._IExpression> defaultValue, bool isStatic) {
      parent.AddUnsupported("Datatype field " + item.dtor_name);
    }

    public object Finish() {
      parent.AddDatatype((Datatype)Datatype.create(
        Sequence<Rune>.UnicodeFromString(this.name),
        Sequence<Rune>.UnicodeFromString(this.docString),
        Sequence<Rune>.UnicodeFromString(this.enclosingModule),
        Sequence<DAST.TypeArgDecl>.FromArray(typeParams.ToArray()),
        Sequence<DAST.DatatypeCtor>.FromArray(ctors.ToArray()),
        Sequence<DAST.Method>.FromArray(body.ToArray()),
        this.isCo, equalitySupport, attributes,
        Sequence<DAST.Type>.FromArray(superTraitTypes.ToArray()),
          Sequence<DAST.Type>.FromArray(superNegativeTraitTypes.ToArray())
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
      Sequence<DAST.Formal> params_, Sequence<DAST.Formal> inheritedParams,
      List<DAST.Type> outTypes, List<ISequence<Rune>> outVars) {
      return new MethodBuilder(this, isStatic, hasBody, outVarsAreUninitFieldsToAssign, wasFunction, overridingPath, docString, attributes, name, typeArgs, params_, inheritedParams, outTypes, outVars);
    }

    public object Finish();
  }

  class MethodBuilder : StatementContainer {
    readonly ClassLike parent;
    readonly string name;
    readonly bool isStatic;
    readonly bool hasBody;
    readonly bool outVarsAreUninitFieldsToAssign;
    readonly bool wasFunction;
    readonly ISequence<ISequence<Rune>> overridingPath;
    readonly List<DAST.TypeArgDecl> typeArgs;
    readonly Sequence<DAST.Formal> params_;
    readonly Sequence<DAST.Formal> inheritedParams;
    readonly List<DAST.Type> outTypes;
    readonly List<ISequence<Rune>> outVars;
    readonly List<object> body = [];
    private ISequence<_IAttribute> attributes;
    private ISequence<Rune> docString;

    public MethodBuilder(
      ClassLike parent,
      bool isStatic, bool hasBody, bool outVarsAreUninitFieldsToAssign, bool wasFunction,
      ISequence<ISequence<Rune>> overridingPath,
      string docString,
      ISequence<_IAttribute> attributes,
      string name,
      List<DAST.TypeArgDecl> typeArgs,
      Sequence<DAST.Formal> params_, Sequence<DAST.Formal> inheritedParams,
      List<DAST.Type> outTypes, List<ISequence<Rune>> outVars) {
      this.parent = parent;
      this.isStatic = isStatic;
      this.hasBody = hasBody;
      this.outVarsAreUninitFieldsToAssign = outVarsAreUninitFieldsToAssign;
      this.wasFunction = wasFunction;
      this.overridingPath = overridingPath;
      this.docString = Sequence<Rune>.UnicodeFromString(docString);
      this.attributes = attributes;
      this.name = name;
      this.typeArgs = typeArgs;
      this.params_ = params_;
      this.outTypes = outTypes;
      this.outVars = outVars;
      this.inheritedParams = inheritedParams;
    }

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
        Sequence<Rune>.UnicodeFromString(this.name),
        Sequence<DAST.TypeArgDecl>.FromArray(typeArgs.ToArray()),
        params_,
        inheritedParams,
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

    public CallStmtBuilder Call(_ICallSignature signature) {
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

  class ForkedStatementContainer : StatementContainer {
    readonly List<object> list;

    public ForkedStatementContainer(List<object> list) {
      this.list = list;
    }

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

  class DeclareBuilder : ExprContainer, BuildableStatement {
    readonly DAST.Type type;
    readonly string name;
    public object value;

    public DeclareBuilder(DAST.Type type, string name) {
      this.type = type;
      this.name = name;
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

  class ElseBuilder : StatementContainer {
    public readonly IfElseBuilder parent;

    public ElseBuilder(IfElseBuilder parent) {
      this.parent = parent;
    }

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

  class ForeachBuilder : ExprContainer, StatementContainer, BuildableStatement {
    readonly string boundName;
    readonly DAST.Type boundType;
    object over = null;
    readonly List<object> body = [];

    public ForeachBuilder(string boundName, DAST.Type boundType) {
      this.boundName = boundName;
      this.boundType = boundType;
    }

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

  class CallStmtBuilder : ExprContainer, BuildableStatement {
    object on = null;
    DAST.CallName name = null;
    List<DAST.Type> typeArgs = null;
    readonly List<object> args = [];
    List<ISequence<Rune>> outs = null;
    public readonly _ICallSignature Signature;

    public CallStmtBuilder(_ICallSignature signature) {
      this.Signature = signature;
    }

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

  class LabeledBuilder : BuildableStatement, StatementContainer {
    readonly string label;
    readonly List<object> statements = [];

    public LabeledBuilder(string label) {
      this.label = label;
    }

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

  class ExprWrapper : ExprContainer, BuildableExpr {
    public Func<DAST.Expression, DAST.Expression> InternalWrapper;
    [CanBeNull] public object Expr;

    public ExprWrapper(Func<DAST.Expression, DAST.Expression> internalWrapper = null) {
      this.InternalWrapper = internalWrapper;
    }

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

  class ExprBuffer : ExprContainer, BuildableExpr {
    Stack<object> exprs = new();
    public readonly object parent;

    public ExprBuffer(object returnTo) {
      this.parent = returnTo;
    }

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

    CallExprBuilder Call(_ICallSignature signature) {
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

  class ArrayLhs : BuildableLhs, ExprContainer {
    readonly List<DAST.Expression> indices;
    object arrayExpr = null;
    readonly System.Diagnostics.StackTrace stackTrace = new(true);

    public ArrayLhs(List<DAST.Expression> indices) {
      this.indices = indices;
    }

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

  class CallExprBuilder : ExprContainer, BuildableExpr {
    object on = null;
    DAST.CallName name = null;
    List<DAST.Type> typeArgs = null;
    readonly List<object> args = [];
    List<ISequence<Rune>> outs = null;

    public _ICallSignature Signature { get; }

    public CallExprBuilder(_ICallSignature signature) {
      Signature = signature;
    }

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

  class LambdaExprBuilder : StatementContainer, BuildableExpr {
    readonly List<DAST.Formal> formals;
    readonly DAST.Type retType;
    readonly List<object> body = [];

    public LambdaExprBuilder(List<DAST.Formal> formals, DAST.Type retType) {
      this.formals = formals;
      this.retType = retType;
    }

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

  class IIFEExprBuilder : ExprContainer, BuildableExpr {
    readonly string name;
    readonly DAST.Type tpe;

    object body = null;
    public object value = null;

    public IIFEExprBuilder(string name, DAST.Type tpe) {
      this.name = name;
      this.tpe = tpe;
    }

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

  class IIFEExprRhs : ExprContainer {
    readonly IIFEExprBuilder parent;

    public IIFEExprRhs(IIFEExprBuilder parent) {
      this.parent = parent;
    }

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

  class BetaRedexBuilder : ExprContainer, BuildableExpr {
    readonly List<_System.Tuple2<DAST.Formal, DAST.Expression>> bindings;
    readonly DAST.Type retType;
    object body = null;

    public BetaRedexBuilder(List<_System.Tuple2<DAST.Formal, DAST.Expression>> bindings, DAST.Type retType) {
      this.bindings = bindings;
      this.retType = retType;
    }

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

  class ConvertBuilder : ExprContainer, BuildableExpr {
    readonly DAST.Type fromType;
    readonly DAST.Type toType;
    object value = null;

    public ConvertBuilder(DAST.Type fromType, DAST.Type toType) {
      this.fromType = fromType;
      this.toType = toType;
    }

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

  class IndexBuilder : ExprContainer, BuildableExpr {
    readonly List<DAST.Expression> indices;
    readonly DAST._ICollKind collKind;
    object value = null;

    public IndexBuilder(List<DAST.Expression> indices, DAST._ICollKind collKind) {
      this.indices = indices;
      this.collKind = collKind;
    }

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

  class NativeRangeBuilder : ExprContainer, BuildableExpr {
    [CanBeNull] readonly string start;
    [CanBeNull] object bound;

    public NativeRangeBuilder(string start = null) {
      this.start = start;
      bound = null;
    }

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

  class ArrayLengthBuilder : ExprContainer, BuildableExpr {
    private readonly DAST.Type arrayType;
    private readonly int dim;
    private object array;
    private readonly bool native;

    public ArrayLengthBuilder(DAST.Type arrayType, int dim, bool native) {
      this.arrayType = arrayType;
      this.dim = dim;
      this.native = native;
      array = null;
    }

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
