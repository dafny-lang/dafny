using System;
using System.Collections.Generic;
using System.Linq;
using DafnyServer.CounterexampleGeneration;
using Microsoft.Dafny;
using Function = Microsoft.Dafny.Function;
using Program = Microsoft.Dafny.Program;
using Type = Microsoft.Dafny.Type;

namespace DafnyTestGeneration {

  /// <summary> Extract essential info from a parsed Dafny program </summary>
  public class DafnyInfo {

    // method -> list of return types
    private readonly Dictionary<string, List<Type>> returnTypes;
    private readonly Dictionary<string, List<Type>> parameterTypes;
    private readonly HashSet<string> isStatic; // static methods
    private readonly HashSet<string> isNotGhost; // ghost methods
    private readonly Dictionary<string, int> nOfTypeParams;
    // import required to access the code contained in the program
    public readonly Dictionary<string, string> ToImportAs;
    public readonly Dictionary<string, IndDatatypeDecl> Datatypes;
    // TODO: what if it takes type arguments?
    public readonly Dictionary<string, Type> SubsetTypeToSuperset;

    public DafnyInfo(Program program) {
      returnTypes = new Dictionary<string, List<Type>>();
      parameterTypes = new Dictionary<string, List<Type>>();
      isStatic = new HashSet<string>();
      isNotGhost = new HashSet<string>();
      ToImportAs = new Dictionary<string, string>();
      Datatypes = new Dictionary<string, IndDatatypeDecl>();
      nOfTypeParams = new Dictionary<string, int>();
      SubsetTypeToSuperset = new Dictionary<string, Type>();
      SubsetTypeToSuperset["_System.string"] = new SeqType(new CharType());
      SubsetTypeToSuperset["_System.nat"] = Type.Int;
      var visitor = new DafnyInfoExtractor(this);
      visitor.Visit(program);
    }

    public IList<Type> GetReturnTypes(string method) {
      return returnTypes[method];
    }

    public int GetNOfTypeParams(string method) {
      return nOfTypeParams[method];
    }
    
    public IList<Type> GetParameterTypes(string method) {
      return parameterTypes[method];
    }

    public bool IsStatic(string method) {
      return isStatic.Contains(method);
    }
    
    public bool IsGhost(string method) {
      return !isNotGhost.Contains(method);
    }

    /// <summary>
    /// Fills in the Dafny Info data by traversing the AST
    /// </summary>
    private class DafnyInfoExtractor : BottomUpVisitor {

      private readonly DafnyInfo info;

      // path to a method in the tree of modules and classes:
      private bool insideAClass; // method is inside a class (not static)

      internal DafnyInfoExtractor(DafnyInfo info) {
        this.info = info;
        insideAClass = false;
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

        info.SubsetTypeToSuperset[name] = type;
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
        info.SubsetTypeToSuperset[name] = type;
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
        insideAClass = true;
        d.Members.ForEach(Visit);
        insideAClass = false;
      }

      private void Visit(ClassDecl d) {
        if (d.Name == "_default") {
          insideAClass = false; // methods in _default are considered static
          d.Members.ForEach(Visit);
          return;
        }
        insideAClass = true;
        d.Members.ForEach(Visit);
        insideAClass = false;
      }

      private void Visit(MemberDecl d) {
        if (d is Method method) {
          Visit(method);
        } else if (d is Function function) {
          Visit(function);
        } 
      }

      private new void Visit(Method m) {
        var methodName = m.FullDafnyName;
        if (m.HasStaticKeyword || !insideAClass) {
          info.isStatic.Add(methodName);
        }
        if (!m.IsLemmaLike && !m.IsGhost) {
          info.isNotGhost.Add(methodName);
        }
        var returnTypes = m.Outs.Select(arg => 
          DafnyModelTypeUtils.UseFullName(arg.Type)).ToList();
        var parameterTypes = m.Ins.Select(arg => 
          DafnyModelTypeUtils.UseFullName(arg.Type)).ToList();
        info.parameterTypes[methodName] = parameterTypes;
        info.returnTypes[methodName] = returnTypes;
        info.nOfTypeParams[methodName] = m.TypeArgs.Count;
      }

      private new void Visit(Function f) {
        var functionName = f.FullDafnyName;
        if (f.HasStaticKeyword || !insideAClass) {
          info.isStatic.Add(functionName);
        }
        if (!f.IsGhost) {
          info.isNotGhost.Add(functionName);
        }
        var returnTypes = new List<Type> { DafnyModelTypeUtils.UseFullName(f.ResultType) };
        var parameterTypes = f.Formals.Select(f => 
          DafnyModelTypeUtils.UseFullName(f.Type)).ToList();
        info.parameterTypes[functionName] = parameterTypes;
        info.returnTypes[functionName] = returnTypes;
        info.nOfTypeParams[functionName] = f.TypeArgs.Count;
      }
    }
  }
}