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

  class ModuleBuilder : ClassContainer, NewtypeContainer {
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

    public object Finish() {
      parent.AddModule((Module)Module.create(Sequence<Rune>.UnicodeFromString(this.name), Sequence<ModuleItem>.FromArray(body.ToArray())));
      return parent;
    }
  }

  interface NewtypeContainer {
    DafnyCompiler compiler { get; }
    void AddNewtype(Newtype item);
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

  interface MethodContainer {
    DafnyCompiler compiler { get; }
    void AddMethod(DAST.Method item);

    public MethodBuilder Method(string name) {
      return new MethodBuilder(this, name);
    }
  }

  class MethodBuilder : StatementContainer {
    public DafnyCompiler compiler { get => parent.compiler; }
    readonly MethodContainer parent;
    readonly string name;
    readonly List<DAST.Statement> body = new();

    public MethodBuilder(MethodContainer parent, string name) {
      this.parent = parent;
      this.name = name;
    }

    public void AddStatement(DAST.Statement item) {
      body.Add(item);
    }

    public object Finish() {
      parent.AddMethod((DAST.Method)DAST.Method.create(Sequence<Rune>.UnicodeFromString(this.name), Sequence<DAST.Statement>.FromArray(body.ToArray())));
      return parent;
    }
  }

  interface StatementContainer {
    DafnyCompiler compiler { get; }
    void AddStatement(DAST.Statement item);

    public void Print(DAST.Expression expr) {
      AddStatement((DAST.Statement)DAST.Statement.create_Print(expr));
    }

    public AssignBuilder Assign() {
      return new AssignBuilder(this, false, null);
    }

    public AssignBuilder DeclareAndAssign(DAST.Type type) {
      return new AssignBuilder(this, true, type);
    }
  }

  class AssignBuilder : ExprContainer {
    public DafnyCompiler compiler { get => parent.compiler; }
    readonly StatementContainer parent;
    readonly bool isDeclare;
    readonly DAST.Type type;
    string name = null;
    DAST.Expression value;

    public AssignBuilder(StatementContainer parent, bool isDeclare, DAST.Type type) {
      this.parent = parent;
      this.isDeclare = isDeclare;
      this.type = type;
    }

    public void SetName(string name) {
      if (this.name != null) {
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
          compiler.currentBuilder = this.Finish();
        } else {
          throw new InvalidOperationException();
        }
      }
    }

    public object Finish() {
      if (isDeclare) {
        parent.AddStatement((DAST.Statement)DAST.Statement.create_DeclareVar(Sequence<Rune>.UnicodeFromString(name), type, value));
      } else {
        parent.AddStatement((DAST.Statement)DAST.Statement.create_Assign(Sequence<Rune>.UnicodeFromString(name), value));
      }
      return parent;
    }
  }

  interface ExprContainer {
    DafnyCompiler compiler { get; }
    void AddExpr(DAST.Expression item);

    public void PassThrough(string expr) {
      AddExpr((DAST.Expression)DAST.Expression.create_PassThroughExpr(Sequence<Rune>.UnicodeFromString(expr)));
    }
  }

}
