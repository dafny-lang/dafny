using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny;
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
    public readonly HashSet<string> DatatypeNames;

    public DafnyInfo(Program program) {
      returnTypes = new Dictionary<string, List<Type>>();
      parameterTypes = new Dictionary<string, List<Type>>();
      isStatic = new HashSet<string>();
      isNotGhost = new HashSet<string>();
      ToImportAs = new Dictionary<string, string>();
      DatatypeNames = new HashSet<string>();
      nOfTypeParams = new Dictionary<string, int>();
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
      private readonly List<string> path;
      private bool insideAClass; // method is inside a class (not static)

      internal DafnyInfoExtractor(DafnyInfo info) {
        this.info = info;
        insideAClass = false;
        path = new List<string>();
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
        }
      }

      private void Visit(LiteralModuleDecl d) {
        if (d.ModuleDef.IsAbstract) {
          return;
        }
        if (d.Name.Equals("_module")) {
          d.ModuleDef.TopLevelDecls.ForEach(Visit);
          return;
        }
        path.Add(d.Name);
        if (info.ToImportAs.ContainsValue(d.Name)) {
          var id = info.ToImportAs.Values.Count(v => v.StartsWith(d.Name));
          info.ToImportAs[string.Join(".", path)] = d.Name + id;
        } else {
          info.ToImportAs[string.Join(".", path)] = d.Name;
        }
        d.ModuleDef.TopLevelDecls.ForEach(Visit);
        path.RemoveAt(path.Count - 1);
      }

      private void Visit(IndDatatypeDecl d) {
        path.Add(d.Name);
        info.DatatypeNames.Add(string.Join(".", path));
        insideAClass = true;
        d.Members.ForEach(Visit);
        insideAClass = false;
        path.RemoveAt(path.Count - 1);
      }

      private void Visit(ClassDecl d) {
        if (d.Name == "_default") {
          insideAClass = false; // methods in _default are considered static
          d.Members.ForEach(Visit);
          return;
        }
        insideAClass = true;
        path.Add(d.Name);
        d.Members.ForEach(Visit);
        path.RemoveAt(path.Count - 1);
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
        var methodName = m.Name;
        if (path.Count != 0) {
          methodName = $"{string.Join(".", path)}.{methodName}";
        }
        if (m.HasStaticKeyword || !insideAClass) {
          info.isStatic.Add(methodName);
        }
        if (!m.IsLemmaLike && !m.IsGhost) {
          info.isNotGhost.Add(methodName);
        }
        var returnTypes = m.Outs.Select(arg => arg.Type).ToList();
        var parameterTypes = m.Ins.Select(arg => arg.Type).ToList();
        info.parameterTypes[methodName] = parameterTypes;
        info.returnTypes[methodName] = returnTypes;
        info.nOfTypeParams[methodName] = m.TypeArgs.Count;
      }

      private new void Visit(Function f) {
        var methodName = f.Name;
        if (path.Count != 0) {
          methodName = $"{string.Join(".", path)}.{methodName}";
        }
        if (f.HasStaticKeyword || !insideAClass) {
          info.isStatic.Add(methodName);
        }
        if (!f.IsGhost) {
          info.isNotGhost.Add(methodName);
        }
        var returnTypes = new List<Type> { f.ResultType };
        var parameterTypes = f.Formals.Select(f => f.Type).ToList();
        info.parameterTypes[methodName] = parameterTypes;
        info.returnTypes[methodName] = returnTypes;
        info.nOfTypeParams[methodName] = f.TypeArgs.Count;
      }
    }
  }
}