using System;
using System.Collections.Generic;
using Dafny;
using DAST;

namespace Microsoft.Dafny.Compilers {

  class ProgramBuilder : ModuleContainer {
    readonly List<Module> items = new();

    public void AddModule(Module item) {
      items.Add(item);
    }

    public List<Module> Finish() {
      return items;
    }
  }

  interface ModuleContainer {
    void AddModule(Module item);

    public ModuleBuilder Module(string name) {
      return new ModuleBuilder(this, name);
    }
  }

  class ModuleBuilder : ClassContainer, NewtypeContainer, DatatypeContainer {
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
    void AddClass(Class item);

    public ClassBuilder Class(string name) {
      return new ClassBuilder(this, name);
    }
  }

  class ClassBuilder : ClassLike {
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
    void AddNewtype(Newtype item);

    public NewtypeBuilder Newtype(string name, DAST.Type baseType) {
      return new NewtypeBuilder(this, name, baseType);
    }
  }

  class NewtypeBuilder : ClassLike {
    readonly NewtypeContainer parent;
    readonly string name;
    readonly DAST.Type baseType;

    public NewtypeBuilder(NewtypeContainer parent, string name, DAST.Type baseType) {
      this.parent = parent;
      this.name = name;
      this.baseType = baseType;
    }

    public void AddMethod(DAST.Method item) {
      throw new NotImplementedException();
    }

    public void AddField(DAST.Formal item) {
      throw new NotImplementedException();
    }

    public object Finish() {
      parent.AddNewtype((Newtype)Newtype.create(Sequence<Rune>.UnicodeFromString(this.name), this.baseType));
      return parent;
    }
  }

  interface DatatypeContainer {
    void AddDatatype(Datatype item);

    public DatatypeBuilder Datatype(string name, ISequence<Rune> enclosingModule, List<DAST.Type> typeParams, List<DAST.DatatypeCtor> ctors) {
      return new DatatypeBuilder(this, name, enclosingModule, typeParams, ctors);
    }
  }

  class DatatypeBuilder : ClassLike {
    readonly DatatypeContainer parent;
    readonly string name;
    readonly ISequence<Rune> enclosingModule;
    readonly List<DAST.Type> typeParams;
    readonly List<DAST.DatatypeCtor> ctors;
    readonly List<ClassItem> body = new();

    public DatatypeBuilder(DatatypeContainer parent, string name, ISequence<Rune> enclosingModule, List<DAST.Type> typeParams, List<DAST.DatatypeCtor> ctors) {
      this.parent = parent;
      this.name = name;
      this.typeParams = typeParams;
      this.enclosingModule = enclosingModule;
      this.ctors = ctors;
    }

    public void AddMethod(DAST.Method item) {
      body.Add((ClassItem)ClassItem.create_Method(item));
    }

    public void AddField(DAST.Formal item) {
      throw new NotImplementedException();
    }

    public object Finish() {
      parent.AddDatatype((Datatype)Datatype.create(
        Sequence<Rune>.UnicodeFromString(this.name),
        this.enclosingModule,
        Sequence<DAST.Type>.FromArray(typeParams.ToArray()),
        Sequence<DAST.DatatypeCtor>.FromArray(ctors.ToArray()),
        Sequence<ClassItem>.FromArray(body.ToArray())
      ));
      return parent;
    }
  }

  interface ClassLike {
    void AddMethod(DAST.Method item);

    void AddField(DAST.Formal item);

    public MethodBuilder Method(bool isStatic, string name, List<DAST.Type> typeArgs, List<DAST.Formal> params_, List<DAST.Type> outTypes, List<ISequence<Rune>> outVars) {
      return new MethodBuilder(this, isStatic, name, typeArgs, params_, outTypes, outVars);
    }

    public object Finish();
  }

  class MethodBuilder : StatementContainer {
    readonly ClassLike parent;
    readonly string name;
    readonly bool isStatic;
    readonly List<DAST.Type> typeArgs;
    readonly List<DAST.Formal> params_;
    readonly List<DAST.Type> outTypes;
    readonly List<ISequence<Rune>> outVars;
    readonly List<object> body = new();

    public MethodBuilder(ClassLike parent, bool isStatic, string name, List<DAST.Type> typeArgs, List<DAST.Formal> params_, List<DAST.Type> outTypes, List<ISequence<Rune>> outVars) {
      this.parent = parent;
      this.isStatic = isStatic;
      this.name = name;
      this.typeArgs = typeArgs;
      this.params_ = params_;
      this.outTypes = outTypes;
      this.outVars = outVars;
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
        isStatic,
        Sequence<Rune>.UnicodeFromString(this.name),
        Sequence<DAST.Type>.FromArray(typeArgs.ToArray()),
        Sequence<DAST.Formal>.FromArray(params_.ToArray()),
        Sequence<DAST.Statement>.FromArray(builtStatements.ToArray()),
        Sequence<DAST.Type>.FromArray(outTypes.ToArray()),
        outVars != null ? Optional<ISequence<ISequence<Rune>>>.create_Some(Sequence<ISequence<Rune>>.FromArray(outVars.ToArray())) : Optional<ISequence<ISequence<Rune>>>.create_None()
      );
    }
  }

  interface StatementContainer {
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

    public CallStmtBuilder Call(object returnTo) {
      return new CallStmtBuilder(this, returnTo);
    }

    public ReturnBuilder Return() {
      return new ReturnBuilder(this);
    }
  }

  interface BuildableStatement {
    DAST.Statement Build();
  }

  class AssignBuilder : ExprContainer, BuildableStatement {
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
        if (this.value == null) {
          throw new InvalidOperationException("Cannot assign null value to variable: " + name);
        } else {
          return (DAST.Statement)DAST.Statement.create_Assign(Sequence<Rune>.UnicodeFromString(name), value);
        }
      }
    }
  }

  class IfElseBuilder : ExprContainer, StatementContainer, BuildableStatement {
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

  class CallStmtBuilder : ExprContainer {
    public readonly StatementContainer parent;
    public readonly object returnTo;

    DAST.Expression on = null;
    string name = null;
    List<DAST.Type> typeArgs = null;
    readonly List<DAST.Expression> args = new();
    List<ISequence<Rune>> outs = null;

    public CallStmtBuilder(StatementContainer parent, object returnTo) {
      this.parent = parent;
      this.returnTo = returnTo;
    }

    public void SetName(string name) {
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

    public void SetOuts(List<ISequence<Rune>> outs) {
      if (this.outs != null) {
        throw new InvalidOperationException();
      } else {
        this.outs = outs;
      }
    }

    public void Finish() {
      parent.AddStatement((DAST.Statement)DAST.Statement.create_Call(
        on,
        Sequence<Rune>.UnicodeFromString(name),
        Sequence<DAST.Type>.FromArray(typeArgs.ToArray()),
        Sequence<DAST.Expression>.FromArray(args.ToArray()),
        outs == null ? DAST.Optional<ISequence<ISequence<Rune>>>.create_None() : DAST.Optional<ISequence<ISequence<Rune>>>.create_Some(Sequence<ISequence<Rune>>.FromArray(outs.ToArray()))
      ));
    }
  }

  class ReturnBuilder : ExprContainer {
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

  class ExprBuffer : ExprContainer {
    Stack<DAST.Expression> exprs = new();
    public readonly object parent;

    public ExprBuffer(object returnTo) {
      this.parent = returnTo;
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
        throw new InvalidOperationException("Expected exactly one expression in buffer, got " + exprs.Comma(e => e.ToString()));
      } else {
        return exprs.Pop();
      }
    }
  }

  interface ExprContainer {
    void AddExpr(DAST.Expression item);

    BinOpBuilder BinOp(string op, DafnyCompiler compiler, object returnTo) {
      return new BinOpBuilder(compiler, this, op, returnTo);
    }

    CallExprBuilder Call() {
      return new CallExprBuilder(this);
    }
  }

  class BinOpBuilder : ExprContainer {
    readonly DafnyCompiler compiler;
    readonly ExprContainer parent;
    readonly string op;
    readonly object returnTo;
    DAST.Expression left = null;
    DAST.Expression right = null;

    public BinOpBuilder(DafnyCompiler compiler, ExprContainer parent, string op, object returnTo) {
      this.compiler = compiler;
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

    public void Finish() {
      parent.AddExpr((DAST.Expression)DAST.Expression.create_BinOp(Sequence<Rune>.UnicodeFromString(op), left, right));
    }
  }

  class CallExprBuilder : ExprContainer {
    public readonly ExprContainer parent;

    DAST.Expression on = null;
    string name = null;
    List<DAST.Type> typeArgs = null;
    readonly List<DAST.Expression> args = new();
    List<ISequence<Rune>> outs = null;

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

    public void SetOuts(List<ISequence<Rune>> outs) {
      if (this.outs != null) {
        throw new InvalidOperationException();
      } else {
        this.outs = outs;
      }
    }

    public object Finish() {
      parent.AddExpr((DAST.Expression)DAST.Expression.create_Call(
        on,
        Sequence<Rune>.UnicodeFromString(name),
        Sequence<DAST.Type>.FromArray(typeArgs.ToArray()),
        Sequence<DAST.Expression>.FromArray(args.ToArray())
      ));

      return parent;
    }
  }

}
