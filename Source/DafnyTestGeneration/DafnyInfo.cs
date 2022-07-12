using System;
using System.Collections.Generic;
using System.Linq;
using DafnyServer.CounterexampleGeneration;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Function = Microsoft.Dafny.Function;
using IdentifierExpr = Microsoft.Dafny.IdentifierExpr;
using LetExpr = Microsoft.Dafny.LetExpr;
using OldExpr = Microsoft.Dafny.OldExpr;
using Program = Microsoft.Dafny.Program;
using Type = Microsoft.Dafny.Type;

namespace DafnyTestGeneration {

  /// <summary> Extract essential info from a parsed Dafny program </summary>
  public class DafnyInfo {
    
    private readonly Dictionary<string, Method> methods;
    private readonly Dictionary<string, Function> functions;
    public readonly Dictionary<string, IndDatatypeDecl> Datatypes;
    // import required to access the code contained in the program
    public readonly Dictionary<string, string> ToImportAs;
    // TODO: what if it takes type arguments?
    private readonly Dictionary<string, Type> subsetTypeToSuperset;
    // list of top level scopes accessible from the testing module
    private readonly List<VisibilityScope> scopes;

    public DafnyInfo(Program program) {
      methods = new Dictionary<string, Method>();
      functions = new Dictionary<string, Function>();
      ToImportAs = new Dictionary<string, string>();
      Datatypes = new Dictionary<string, IndDatatypeDecl>();
      subsetTypeToSuperset = new Dictionary<string, Type>();
      subsetTypeToSuperset["_System.string"] = new SeqType(new CharType());
      subsetTypeToSuperset["string"] = new SeqType(new CharType());
      subsetTypeToSuperset["_System.nat"] = Type.Int;
      subsetTypeToSuperset["nat"] = Type.Int;
      subsetTypeToSuperset["_System.object"] = new UserDefinedType(new Token(), "object", new List<Type>());
      scopes = program.DefaultModuleDef.TopLevelDecls?
        .OfType<LiteralModuleDecl>()
        .Select(declaration => 
          declaration.DefaultExport.VisibilityScope).ToList() ?? new List<VisibilityScope>();
      var visitor = new DafnyInfoExtractor(this);
      visitor.Visit(program);
    }

    public IList<Type> GetReturnTypes(string callable) {
      if (methods.ContainsKey(callable)) {
        return methods[callable].Outs.Select(arg => 
          DafnyModelTypeUtils.UseFullName(arg.Type)).ToList();;
      } 
      if (functions.ContainsKey(callable)) {
        return new List<Type>
          { DafnyModelTypeUtils.UseFullName(functions[callable].ResultType) };
      }
      throw new Exception("Cannot identify callable " + callable);
    }

    public int GetNOfTypeArgs(string callable) {
      if (methods.ContainsKey(callable)) {
        return methods[callable].TypeArgs.Count;
      } 
      if (functions.ContainsKey(callable)) {
        return functions[callable].TypeArgs.Count;
      }
      throw new Exception("Cannot identify callable " + callable);
    }
    
    public IList<Type> GetFormalsTypes(string callable) {
      if (methods.ContainsKey(callable)) {
        return methods[callable].Ins.Select(arg => 
          DafnyModelTypeUtils.UseFullName(arg.Type)).ToList();;
      } 
      if (functions.ContainsKey(callable)) {
        return functions[callable].Formals.Select(arg => 
          DafnyModelTypeUtils.UseFullName(arg.Type)).ToList();;
      }
      throw new Exception("Cannot identify callable " + callable);
    }

    public bool IsStatic(string callable) {
      if (methods.ContainsKey(callable)) {
        return methods[callable].IsStatic;
      } 
      if (functions.ContainsKey(callable)) {
        return functions[callable].IsStatic;
      }
      throw new Exception("Cannot identify callable " + callable);
    }
    
    public bool IsGhost(string callable) {
      if (methods.ContainsKey(callable)) {
        return methods[callable].IsGhost || methods[callable].IsLemmaLike;
      } 
      if (functions.ContainsKey(callable)) {
        return functions[callable].IsGhost;
      }
      return true;
    }

    public bool IsAccessible(string callable) {
      if (methods.ContainsKey(callable)) {
        return scopes.Any(scope => methods[callable].IsVisibleInScope(scope));
      } 
      if (functions.ContainsKey(callable)) {
        return scopes.Any(scope => functions[callable].IsVisibleInScope(scope));
      }
      return false;
    }

    public Type? GetSupersetType(Type type) {
      if (type is not UserDefinedType userDefinedType ||
          !subsetTypeToSuperset.ContainsKey(userDefinedType.Name)) {
        return null;
      }
      var superSetType = subsetTypeToSuperset[userDefinedType.Name];
      superSetType = DafnyModelTypeUtils.CopyWithReplacements(superSetType,
        superSetType.TypeArgs.ConvertAll(arg =>
          (arg as UserDefinedType)?.Name ?? ""), type.TypeArgs);
      if ((superSetType is UserDefinedType tmp) &&
          (tmp.Name.StartsWith("_System") &&
           subsetTypeToSuperset.ContainsKey(tmp.Name))) {
        return subsetTypeToSuperset[tmp.Name];
      }
      return superSetType;
    }
    
    public IEnumerable<Expression> GetEnsures(List<string> ins, List<string> outs, string callableName, string receiver) {
      Dictionary<IVariable, string> subst = new Dictionary<IVariable, string>();
      if (methods.ContainsKey(callableName)) {
        for (int i = 0; i < methods[callableName].Ins.Count; i++) {
          subst[methods[callableName].Ins[i]] = ins[i];
        }
        for (int i = 0; i < methods[callableName].Outs.Count; i++) {
          subst[methods[callableName].Outs[i]] = outs[i];
        }
        return methods[callableName].Ens.Select(e =>
            new ClonerWithSubstitution(this, subst, receiver).CloneValidOrNull(e.E))
          .Where(e => e != null);
      } 
      if (functions.ContainsKey(callableName)) {
        for (int i = 0; i < functions[callableName].Formals.Count; i++) {
          subst[functions[callableName].Formals[i]] = ins[i];
        }

        if (functions[callableName].Result != null) {
          subst[functions[callableName].Result] = outs[0];
        }

        return functions[callableName].Ens.Select(e =>
            new ClonerWithSubstitution(this, subst, receiver).CloneValidOrNull(e.E))
          .Where(e => e != null);
      }
      throw new Exception("Cannot identify callable " + callableName);
    }

    /// <summary>
    /// Fills in the Dafny Info data by traversing the AST
    /// </summary>
    private class DafnyInfoExtractor : BottomUpVisitor {

      private readonly DafnyInfo info;

      internal DafnyInfoExtractor(DafnyInfo info) {
        this.info = info;
      }

      internal void Visit(Program p) {
        Visit(p.DefaultModule);
      }

      private void Visit(TopLevelDecl d) {
        if (d is LiteralModuleDecl moduleDecl) {
          Visit(moduleDecl);
        } else if (d is ClassDecl classDecl) {
          Visit(classDecl);
        } else if (d is IndDatatypeDecl datatypeDecl) {
          Visit(datatypeDecl);
        } else if (d is NewtypeDecl newTypeDecl) {
          Visit(newTypeDecl);
        } else if (d is TypeSynonymDeclBase typeSynonymDecl) {
          Visit(typeSynonymDecl);
        }
      }
      
      private new void Visit(NewtypeDecl newType) {
        var name = newType.FullDafnyName;
        var type = newType.BaseType;
        while (type is InferredTypeProxy inferred) {
          type = inferred.T;
        }
        type = DafnyModelTypeUtils.UseFullName(type);
        if (DafnyOptions.O.TestGenOptions.Verbose) {
          Console.Out.WriteLine($"// Warning: Values of type {name} will be " +
                                $"assigned a default value of type {type}, " +
                                $"which may or may not match the associated " +
                                $"condition");
        }

        info.subsetTypeToSuperset[name] = type;
      }

      private void Visit(TypeSynonymDeclBase newType) {
        var name = newType.FullDafnyName;
        var type = newType.Rhs;
        while (type is InferredTypeProxy inferred) {
          type = inferred.T;
        }
        type = DafnyModelTypeUtils.UseFullName(type);
        if (DafnyOptions.O.TestGenOptions.Verbose) {
          Console.Out.WriteLine($"// Warning: Values of type {name} will be " +
                                $"assigned a default value of type {type}, " +
                                $"which may or may not match the associated " +
                                $"condition");
        }
        info.subsetTypeToSuperset[name] = type;
      }
      private void Visit(LiteralModuleDecl d) {
        if (d.ModuleDef.IsAbstract) {
          return;
        }
        if (info.ToImportAs.ContainsValue(d.Name)) {
          var id = info.ToImportAs.Values.Count(v => v.StartsWith(d.Name));
          info.ToImportAs[d.FullDafnyName] = d.Name + id;
        } else if (d.FullDafnyName != "") {
          info.ToImportAs[d.FullDafnyName] = d.Name;
        }
        d.ModuleDef.TopLevelDecls.ForEach(Visit);
      }

      private void Visit(IndDatatypeDecl d) {
        info.Datatypes[d.FullDafnyName] = d;
        info.Datatypes[d.FullSanitizedName] = d;
        d.Members.ForEach(Visit);
      }

      private void Visit(ClassDecl d) {
        d.Members.ForEach(Visit);
      }

      private void Visit(MemberDecl d) {
        if (d is Method method) {
          Visit(method);
        } else if (d is Function function) {
          Visit(function);
        } 
      }

      private new void Visit(Method m) {
        info.methods[m.FullDafnyName] = m;
      }

      private new void Visit(Function f) {
        info.functions[f.FullDafnyName] = f;
      }
    }
    
    private class ClonerWithSubstitution : Cloner {

      private Dictionary<IVariable, string> subst;
      private bool isValidExpression;
      private string receiver;
      private DafnyInfo dafnyInfo;
      public ClonerWithSubstitution(DafnyInfo dafnyInfo, Dictionary<IVariable, string> subst, string receiver) {
        this.subst = subst;
        this.receiver = receiver;
        this.dafnyInfo = dafnyInfo;
        isValidExpression = true;
      }

      public override Type CloneType(Type type) {
        // TODO: type arguments
        if (type is UserDefinedType userDefinedType) {
          var name = userDefinedType?.ResolvedClass?.FullName ??
                     userDefinedType.Name;
          if (name.StartsWith("_System.")) {
            name = name[8..];
          }
          return new UserDefinedType(new Token(), name,
            type.TypeArgs.ConvertAll(CloneType));
        }
        return base.CloneType(type);
      }

      public override Expression CloneExpr(Expression expr) {
        if (expr == null) {
          return null;
        } 
        switch (expr) {
          case ImplicitThisExpr_ConstructorCall:
            isValidExpression = false;
            return base.CloneExpr(expr);
          case ThisExpr:
            return new IdentifierExpr(expr.tok, receiver); 
          case AutoGhostIdentifierExpr:
            isValidExpression = false;
            return base.CloneExpr(expr);
          case ExprDotName or NameSegment or ApplySuffix: {
            if (!expr.WasResolved()) {
              isValidExpression = false;
              return base.CloneExpr(expr);
            }
            if (expr.Resolved is IdentifierExpr or MemberSelectExpr or DatatypeValue) {
              return CloneExpr(expr.Resolved);
            }
            return base.CloneExpr(expr);
          }
          case DatatypeValue datatypeValue:
            if (datatypeValue.Type is UserDefinedType udt &&
                udt.ResolvedClass != null) {
              return new ApplyExpr(new Token(),
                new IdentifierExpr(new Token(),udt.ResolvedClass.FullDafnyName + "." + 
                datatypeValue.MemberName), 
                datatypeValue.Arguments.ConvertAll(CloneExpr));
            }
            isValidExpression = false;
            return base.CloneExpr(expr);
          case IdentifierExpr identifierExpr: {
            if ((identifierExpr.Var != null) && (identifierExpr.Var.IsGhost)) {
              isValidExpression = false;
              return base.CloneExpr(expr);
            }
            if ((identifierExpr.Var != null) &&
                (subst.ContainsKey(identifierExpr.Var))) {
              return new IdentifierExpr(expr.tok, subst[identifierExpr.Var]);
            } 
            return base.CloneExpr(expr);
          }
          case MemberSelectExpr memberSelectExpr: {
            if (memberSelectExpr.Member.IsGhost || 
                dafnyInfo.scopes.All(scope => !memberSelectExpr.Member.IsVisibleInScope(scope))) {
              isValidExpression = false;
              return base.CloneExpr(expr);
            }
            if (memberSelectExpr.Obj is StaticReceiverExpr staticReceiverExpr) {
              return new IdentifierExpr(expr.tok,
                ((staticReceiverExpr.Type) as UserDefinedType).ResolvedClass
                .FullDafnyName + "." + memberSelectExpr.MemberName);
            }
            return base.CloneExpr(expr);
          }
          case OldExpr or UnchangedExpr or FreshExpr or LetExpr or 
            LetOrFailExpr or ComprehensionExpr or WildcardExpr or StmtExpr:
            isValidExpression = false;
            return base.CloneExpr(expr);
          default:
            return base.CloneExpr(expr);
        }
      }
      public Expression? CloneValidOrNull(Expression expr) {
        var result = CloneExpr(expr);
        return isValidExpression ? result : null;
      }
    }
  }
}