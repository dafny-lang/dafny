using System;
using System.Collections.Generic;
using Dafny;
using DAST;

namespace Microsoft.Dafny.Compilers {

  class ProgramBuilder : ModuleContainer {
    public readonly DafnyCompiler _compiler;
    public DafnyCompiler compiler { get => _compiler; }


    readonly List<TopLevel> items = new();

    public ProgramBuilder(DafnyCompiler compiler) {
      _compiler = compiler;
    }

    public void AddModule(Module item) {
      items.Add((TopLevel)TopLevel.create_Module(item));
    }

    public List<TopLevel> Finish() {
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

  class ClassBuilder : MethodContainer {
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

  class NewtypeBuilder : MethodContainer {
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
      // body.Add((NewtypeItem)NewtypeItem.create_Method(item));
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

    public DatatypeBuilder Datatype(string name) {
      return new DatatypeBuilder(this, name);
    }
  }

  class DatatypeBuilder : MethodContainer {
    public DafnyCompiler compiler { get => parent.compiler; }
    readonly DatatypeContainer parent;
    readonly string name;
    // readonly List<?> ctors = new();
    readonly List<ClassItem> body = new();

    public DatatypeBuilder(DatatypeContainer parent, string name) {
      this.parent = parent;
      this.name = name;
    }

    public void AddMethod(DAST.Method item) {
      // body.Add((ClassItem)ClassItem.create_Method(item));
      // TODO
    }

    public object Finish() {
      parent.AddDatatype((Datatype)Datatype.create(Sequence<Rune>.UnicodeFromString(this.name), Sequence<ClassItem>.FromArray(body.ToArray())));
      return parent;
    }
  }

  interface MethodContainer {
    DafnyCompiler compiler { get; }
    void AddMethod(DAST.Method item);

    public MethodBuilder Method(string name, List<DAST.Type> typeArgs) {
      return new MethodBuilder(this, name, typeArgs);
    }

    public object Finish();
  }

  class MethodBuilder : StatementContainer {
    public DafnyCompiler compiler { get => parent.compiler; }
    readonly MethodContainer parent;
    readonly string name;
    readonly List<DAST.Type> typeArgs;
    readonly List<DAST.Statement> body = new();

    public MethodBuilder(MethodContainer parent, string name, List<DAST.Type> typeArgs) {
      this.parent = parent;
      this.name = name;
      this.typeArgs = typeArgs;
    }

    public void AddStatement(DAST.Statement item) {
      body.Add(item);
    }

    public object Finish() {
      parent.AddMethod((DAST.Method)DAST.Method.create(
        Sequence<Rune>.UnicodeFromString(this.name),
        Sequence<DAST.Type>.FromArray(typeArgs.ToArray()),
        Sequence<DAST.Statement>.FromArray(body.ToArray()))
      );
      return parent;
    }
  }

  interface StatementContainer {
    DafnyCompiler compiler { get; }
    void AddStatement(DAST.Statement item);

    public void Print(DAST.Expression expr) {
      AddStatement((DAST.Statement)DAST.Statement.create_Print(expr));
    }

    public AssignBuilder Assign(object returnTo) {
      return new AssignBuilder(this, returnTo, false, null);
    }

    public AssignBuilder DeclareAndAssign(DAST.Type type, object returnTo) {
      return new AssignBuilder(this, returnTo, true, type);
    }

    public CallBuilder Call() {
      return new CallBuilder(this);
    }
  }

  class AssignBuilder : ExprContainer {
    public DafnyCompiler compiler { get => parent.compiler; }
    readonly StatementContainer parent;
    readonly object returnTo;
    readonly bool isDeclare;
    readonly DAST.Type type;
    string name = null;
    DAST.Expression value;

    public AssignBuilder(StatementContainer parent, object returnTo, bool isDeclare, DAST.Type type) {
      this.parent = parent;
      this.returnTo = returnTo;
      this.isDeclare = isDeclare;
      this.type = type;
    }

    public void SetName(string name) {
      if (this.name != null && this.name != name) {
        throw new InvalidOperationException();
      } else {
        this.name = name;
      }
    }

    public void AddExpr(DAST.Expression value) {
      if (this.value != null) {
        throw new InvalidOperationException();
      } else {
        this.value = value;
        if (compiler.currentBuilder == this) {
          compiler.currentBuilder = returnTo;
          this.Finish();
        } else {
          throw new InvalidOperationException();
        }
      }
    }

    public object Finish() {
      if (isDeclare) {
        if (this.value == null) {
          parent.AddStatement((DAST.Statement)DAST.Statement.create_DeclareVar(Sequence<Rune>.UnicodeFromString(name), type, DAST.Optional<DAST._IExpression>.create_None()));
        } else {
          parent.AddStatement((DAST.Statement)DAST.Statement.create_DeclareVar(Sequence<Rune>.UnicodeFromString(name), type, DAST.Optional<DAST._IExpression>.create_Some(this.value)));
        }
      } else {
        parent.AddStatement((DAST.Statement)DAST.Statement.create_Assign(Sequence<Rune>.UnicodeFromString(name), value));
      }
      return parent;
    }
  }

  class CallBuilder : ExprContainer {
    public DafnyCompiler compiler { get => parent.compiler; }
    public readonly StatementContainer parent;

    string name = null;
    readonly List<DAST.Expression> args = new();

    public CallBuilder(StatementContainer parent) {
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
      parent.AddStatement((DAST.Statement)DAST.Statement.create_Todo(
        Sequence<Rune>.UnicodeFromString($"call stmt ({this.name}, {this.args})")
      ));

      return parent;
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
        compiler.currentBuilder = parent;
        return exprs.Pop();
      }
    }
  }

  interface ExprContainer {
    DafnyCompiler compiler { get; }
    void AddExpr(DAST.Expression item);

    BinOpBuilder BinOp(string op) {
      return new BinOpBuilder(this, op);
    }

    CallExprBuilder Call() {
      return new CallExprBuilder(this);
    }
  }

  class BinOpBuilder : ExprContainer {
    public DafnyCompiler compiler { get => parent.compiler; }
    readonly ExprContainer parent;
    readonly string op;
    DAST.Expression left = null;
    DAST.Expression right = null;

    public BinOpBuilder(ExprContainer parent, string op) {
      this.parent = parent;
      this.op = op;
    }

    public void AddExpr(DAST.Expression item) {
      if (left == null) {
        left = item;
      } else if (right == null) {
        right = item;
        if (compiler.currentBuilder == this) {
          compiler.currentBuilder = this.parent;
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
