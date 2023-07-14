using System;
using System.Collections.Generic;
using Dafny;
using DAST;

namespace Microsoft.Dafny.Compilers {

  class ProgramBuilder : ModuleContainer {
    public readonly DafnyCompiler _compiler;
    public DafnyCompiler compiler { get => _compiler; }


    readonly List<Module> items = new();

    public ProgramBuilder(DafnyCompiler compiler) {
      _compiler = compiler;
    }

    public void AddModule(Module item) {
      items.Add(item);
    }

    public List<Module> Finish() {
      return items;
    }
  }

  interface ModuleContainer {
    DafnyCompiler compiler { get; }

    void AddModule(Module item);

    public ModuleBuilder Module(string name) {
      return new ModuleBuilder(this, name);
    }
  }

  class ModuleBuilder : ClassContainer, NewtypeContainer, DatatypeContainer {
    public DafnyCompiler compiler { get => parent.compiler; }
    readonly ModuleContainer parent;
    readonly string name;
    readonly List<ModuleItem> body = new();

    public ModuleBuilder(ModuleContainer parent, string name) {
      this.parent = parent;
      this.name = name;
    }

    public void AddModule(Module item) {
      body.Add((ModuleItem)ModuleItem.create_Module(item));
    }

    public void AddClass(Class item) {
      body.Add((ModuleItem)ModuleItem.create_Class(item));
    }

    public void AddNewtype(Newtype item) {
      body.Add((ModuleItem)ModuleItem.create_Newtype(item));
    }

    public void AddDatatype(Datatype item) {
      body.Add((ModuleItem)ModuleItem.create_Datatype(item));
    }

    public object Finish() {
      parent.AddModule((Module)Module.create(Sequence<Rune>.UnicodeFromString(this.name), Sequence<ModuleItem>.FromArray(body.ToArray())));
      return parent;
    }
  }

  interface ClassContainer {
    DafnyCompiler compiler { get; }
    void AddClass(Class item);

    public ClassBuilder Class(string name) {
      return new ClassBuilder(this, name);
    }
  }

  class ClassBuilder : ClassLike {
    public DafnyCompiler compiler { get => parent.compiler; }
    readonly ClassContainer parent;
    readonly string name;
    readonly List<ClassItem> body = new();

    public ClassBuilder(ClassContainer parent, string name) {
      this.parent = parent;
      this.name = name;
    }

    public void AddMethod(DAST.Method item) {
      body.Add((ClassItem)ClassItem.create_Method(item));
    }

    public void AddField(DAST.Formal item) {
      body.Add((ClassItem)ClassItem.create_Field(item));
    }

    public object Finish() {
      parent.AddClass((Class)Class.create(Sequence<Rune>.UnicodeFromString(this.name), Sequence<ClassItem>.FromArray(body.ToArray())));
      return parent;
    }
  }

  interface NewtypeContainer {
    DafnyCompiler compiler { get; }
    void AddNewtype(Newtype item);

    public NewtypeBuilder Newtype(string name, DAST.Type baseType) {
      return new NewtypeBuilder(this, name, baseType);
    }
  }

  class NewtypeBuilder : ClassLike {
    public DafnyCompiler compiler { get => parent.compiler; }
    readonly NewtypeContainer parent;
    readonly string name;
    readonly DAST.Type baseType;
    // readonly List<NewtypeItem> body = new();

    public NewtypeBuilder(NewtypeContainer parent, string name, DAST.Type baseType) {
      this.parent = parent;
      this.name = name;
      this.baseType = baseType;
    }

    public void AddMethod(DAST.Method item) {
      // TODO
    }

    public void AddField(DAST.Formal item) {
      // TODO
    }

    public object Finish() {
      parent.AddNewtype((Newtype)Newtype.create(Sequence<Rune>.UnicodeFromString(this.name), this.baseType));
      return parent;
    }
  }

  interface DatatypeContainer {
    DafnyCompiler compiler { get; }
    void AddDatatype(Datatype item);

    public DatatypeBuilder Datatype(string name, List<DAST.DatatypeCtor> ctors) {
      return new DatatypeBuilder(this, name, ctors);
    }
  }

  class DatatypeBuilder : ClassLike {
    public DafnyCompiler compiler { get => parent.compiler; }
    readonly DatatypeContainer parent;
    readonly string name;
    readonly List<DAST.DatatypeCtor> ctors;
    readonly List<ClassItem> body = new();

    public DatatypeBuilder(DatatypeContainer parent, string name, List<DAST.DatatypeCtor> ctors) {
      this.parent = parent;
      this.name = name;
      this.ctors = ctors;
    }

    public void AddMethod(DAST.Method item) {
      // TODO
    }

    public void AddField(DAST.Formal item) {
      // TODO
    }

    public object Finish() {
      parent.AddDatatype((Datatype)Datatype.create(
        Sequence<Rune>.UnicodeFromString(this.name),
        Sequence<DAST.DatatypeCtor>.FromArray(ctors.ToArray()),
        Sequence<ClassItem>.FromArray(body.ToArray())
      ));
      return parent;
    }
  }

  interface ClassLike {
    DafnyCompiler compiler { get; }
    void AddMethod(DAST.Method item);

    void AddField(DAST.Formal item);

    public MethodBuilder Method(string name, List<DAST.Type> typeArgs) {
      return new MethodBuilder(this, name, typeArgs);
    }

    public object Finish();
  }

  class MethodBuilder : StatementContainer {
    public DafnyCompiler compiler { get => parent.compiler; }
    readonly ClassLike parent;
    readonly string name;
    readonly List<DAST.Type> typeArgs;
    readonly List<object> body = new();

    public MethodBuilder(ClassLike parent, string name, List<DAST.Type> typeArgs) {
      this.parent = parent;
      this.name = name;
      this.typeArgs = typeArgs;
    }

    public void AddStatement(DAST.Statement item) {
      body.Add(item);
    }

    public void AddBuildable(BuildableStatement item) {
      body.Add(item);
    }

    public DAST.Method Build() {
      List<DAST.Statement> builtStatements = new();
      foreach (var maybeBuilt in body) {
        if (maybeBuilt is DAST.Statement built) {
          builtStatements.Add(built);
        } else if (maybeBuilt is BuildableStatement buildable) {
          builtStatements.Add(buildable.Build());
        } else {
          throw new InvalidOperationException("Unknown buildable type");
        }
      }

      return (DAST.Method)DAST.Method.create(
        Sequence<Rune>.UnicodeFromString(this.name),
        Sequence<DAST.Type>.FromArray(typeArgs.ToArray()),
        Sequence<DAST.Statement>.FromArray(builtStatements.ToArray())
      );
    }
  }

  interface StatementContainer {
    DafnyCompiler compiler { get; }
    void AddStatement(DAST.Statement item);

    void AddBuildable(BuildableStatement item);

    public void Print(DAST.Expression expr) {
      AddStatement((DAST.Statement)DAST.Statement.create_Print(expr));
    }

    public AssignBuilder Assign() {
      var ret = new AssignBuilder(this, false, null);
      AddBuildable(ret);
      return ret;
    }

    public AssignBuilder DeclareAndAssign(DAST.Type type) {
      var ret = new AssignBuilder(this, true, type);
      AddBuildable(ret);
      return ret;
    }

    public IfElseBuilder IfElse() {
      var ret = new IfElseBuilder(this);
      AddBuildable(ret);
      return ret;
    }

    public CallBuilder Call() {
      return new CallBuilder(this);
    }

    public ReturnBuilder Return() {
      return new ReturnBuilder(this);
    }
  }

  interface BuildableStatement {
    DAST.Statement Build();
  }

  class AssignBuilder : ExprContainer, BuildableStatement {
    public DafnyCompiler compiler { get => parent.compiler; }
    public readonly StatementContainer parent;
    readonly bool isDeclare;
    readonly DAST.Type type;
    string name = null;
    public DAST.Expression value;

    public AssignBuilder(StatementContainer parent, bool isDeclare, DAST.Type type) {
      this.parent = parent;
      this.isDeclare = isDeclare;
      this.type = type;
    }

    public void SetName(string name) {
      if (this.name != null && this.name != name) {
        throw new InvalidOperationException("Cannot change name of variable in assignment: " + this.name + " -> " + name);
      } else {
        this.name = name;
      }
    }

    public void AddExpr(DAST.Expression value) {
      if (this.value != null) {
        throw new InvalidOperationException();
      } else {
        this.value = value;
      }
    }

    public DAST.Statement Build() {
      if (isDeclare) {
        if (this.value == null) {
          return (DAST.Statement)DAST.Statement.create_DeclareVar(Sequence<Rune>.UnicodeFromString(name), type, DAST.Optional<DAST._IExpression>.create_None());
        } else {
          return (DAST.Statement)DAST.Statement.create_DeclareVar(Sequence<Rune>.UnicodeFromString(name), type, DAST.Optional<DAST._IExpression>.create_Some(this.value));
        }
      } else {
        return (DAST.Statement)DAST.Statement.create_Assign(Sequence<Rune>.UnicodeFromString(name), value);
      }
    }
  }

  class IfElseBuilder : ExprContainer, StatementContainer, BuildableStatement {
    public DafnyCompiler compiler { get => parent.compiler; }
    public readonly StatementContainer parent;

    DAST.Expression condition = null;
    readonly List<object> ifBody = new();
    readonly List<object> elseBody = new();

    public IfElseBuilder(StatementContainer parent) {
      this.parent = parent;
    }

    public void AddExpr(DAST.Expression value) {
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

    public void AddElseStatement(DAST.Statement item) {
      elseBody.Add(item);
    }

    public void AddElseBuildable(BuildableStatement item) {
      elseBody.Add(item);
    }

    public ElseBuilder Else() {
      return new ElseBuilder(this);
    }

    public DAST.Statement Build() {
      List<DAST.Statement> builtIfStatements = new();
      foreach (var maybeBuilt in ifBody) {
        if (maybeBuilt is DAST.Statement built) {
          builtIfStatements.Add(built);
        } else if (maybeBuilt is BuildableStatement buildable) {
          builtIfStatements.Add(buildable.Build());
        } else {
          throw new InvalidOperationException("Unknown buildable type");
        }
      }

      List<DAST.Statement> builtElseStatements = new();
      foreach (var maybeBuilt in elseBody) {
        if (maybeBuilt is DAST.Statement built) {
          builtElseStatements.Add(built);
        } else if (maybeBuilt is BuildableStatement buildable) {
          builtElseStatements.Add(buildable.Build());
        } else {
          throw new InvalidOperationException("Unknown buildable type");
        }
      }

      return (DAST.Statement)DAST.Statement.create_If(
        condition,
        Sequence<DAST.Statement>.FromArray(builtIfStatements.ToArray()),
        Sequence<DAST.Statement>.FromArray(builtElseStatements.ToArray())
      );
    }
  }

  class ElseBuilder : StatementContainer {
    public DafnyCompiler compiler { get => parent.compiler; }
    public readonly IfElseBuilder parent;

    public ElseBuilder(IfElseBuilder parent) {
      this.parent = parent;
    }

    public void AddStatement(DAST.Statement item) {
      parent.AddElseStatement(item);
    }

    public void AddBuildable(BuildableStatement item) {
      parent.AddElseBuildable(item);
    }
  }

  class CallBuilder : ExprContainer {
    public DafnyCompiler compiler { get => parent.compiler; }
    public readonly StatementContainer parent;

    DAST.Type enclosing = null;
    string name = null;
    readonly List<DAST.Expression> args = new();

    public CallBuilder(StatementContainer parent) {
      this.parent = parent;
    }

    public void SetEnclosing(DAST.Type enclosing) {
      if (this.enclosing != null) {
        throw new InvalidOperationException();
      } else {
        this.enclosing = enclosing;
      }
    }

    public void SetName(string name) {
      if (this.name != null) {
        throw new InvalidOperationException();
      } else {
        this.name = name;
      }
    }

    public void AddExpr(DAST.Expression value) {
      args.Add(value);
    }

    public object Finish() {
      parent.AddStatement((DAST.Statement)DAST.Statement.create_Call(
        enclosing == null ? DAST.Optional<DAST._IType>.create_None() : DAST.Optional<DAST._IType>.create_Some(enclosing),
        Sequence<Rune>.UnicodeFromString(name),
        Sequence<DAST.Expression>.FromArray(args.ToArray())
      ));

      return parent;
    }
  }

  class ReturnBuilder : ExprContainer {
    public DafnyCompiler compiler { get => parent.compiler; }
    readonly StatementContainer parent;

    DAST.Expression value = null;

    public ReturnBuilder(StatementContainer parent) {
      this.parent = parent;
    }

    public void AddExpr(DAST.Expression value) {
      if (this.value != null) {
        throw new InvalidOperationException();
      } else {
        this.value = value;
        parent.AddStatement((DAST.Statement)DAST.Statement.create_Return(value));
      }
    }
  }

  class CallExprBuilder : ExprContainer {
    public DafnyCompiler compiler { get => parent.compiler; }
    readonly ExprContainer parent;

    string name = null;
    readonly List<DAST.Expression> args = new();

    public CallExprBuilder(ExprContainer parent) {
      this.parent = parent;
    }

    public void SetName(string name) {
      if (this.name != null) {
        throw new InvalidOperationException();
      } else {
        this.name = name;
      }
    }

    public void AddExpr(DAST.Expression value) {
      args.Add(value);
    }

    public object Finish() {
      parent.AddExpr((DAST.Expression)DAST.Expression.create_Todo(
        Sequence<Rune>.UnicodeFromString("call expr")
      ));
      return parent;
    }
  }

  class ExprBuffer : ExprContainer {
    public DafnyCompiler compiler { get; }
    Stack<DAST.Expression> exprs = new();
    readonly object parent;

    public ExprBuffer(DafnyCompiler compiler) {
      this.compiler = compiler;
      this.parent = compiler.currentBuilder;
    }

    public void AddExpr(DAST.Expression item) {
      exprs.Push(item);
    }

    public List<DAST.Expression> PopN(int n) {
      if (exprs.Count < n) {
        throw new InvalidOperationException();
      } else {
        var result = new List<DAST.Expression>();
        for (int i = 0; i < n; i++) {
          result.Insert(0, exprs.Pop());
        }
        return result;
      }
    }

    public List<DAST.Expression> PopAll() {
      return PopN(exprs.Count);
    }

    public DAST.Expression Finish() {
      if (exprs.Count != 1) {
        throw new InvalidOperationException();
      } else {
        return exprs.Pop();
      }
    }
  }

  interface ExprContainer {
    DafnyCompiler compiler { get; }
    void AddExpr(DAST.Expression item);

    BinOpBuilder BinOp(string op, object returnTo) {
      return new BinOpBuilder(this, op, returnTo);
    }

    CallExprBuilder Call() {
      return new CallExprBuilder(this);
    }
  }

  class BinOpBuilder : ExprContainer {
    public DafnyCompiler compiler { get => parent.compiler; }
    readonly ExprContainer parent;
    readonly string op;
    readonly object returnTo;
    DAST.Expression left = null;
    DAST.Expression right = null;

    public BinOpBuilder(ExprContainer parent, string op, object returnTo) {
      this.parent = parent;
      this.op = op;
      this.returnTo = returnTo;
    }

    public void AddExpr(DAST.Expression item) {
      if (left == null) {
        left = item;
      } else if (right == null) {
        right = item;
        if (compiler.currentBuilder == this) {
          compiler.currentBuilder = this.returnTo;
          this.Finish();
        } else {
          throw new InvalidOperationException();
        }
      } else {
        throw new InvalidOperationException();
      }
    }

    public object Finish() {
      parent.AddExpr((DAST.Expression)DAST.Expression.create_BinOp(Sequence<Rune>.UnicodeFromString(op), left, right));
      return parent;
    }
  }

}
