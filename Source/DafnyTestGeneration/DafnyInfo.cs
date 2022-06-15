using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny;

namespace DafnyTestGeneration {

  /// <summary> Extract essential info from a parsed Dafny program </summary>
  public class DafnyInfo {

    // method -> list of return types
    private readonly Dictionary<string, List<string>> returnTypes;
    private readonly HashSet<string> isStatic; // static methods
    // import required to access the code contained in the program
    public readonly HashSet<string> ToImport;

    public DafnyInfo(Program program) {
      returnTypes = new Dictionary<string, List<string>>();
      isStatic = new HashSet<string>();
      ToImport = new HashSet<string>();
      var visitor = new DafnyInfoExtractor(this);
      visitor.Visit(program);
    }

    public IList<string> GetReturnTypes(string method) {
      return returnTypes[method];
    }

    public bool IsStatic(string method) {
      return isStatic.Contains(method);
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
        if (d.Name.Equals("_module")) {
          d.ModuleDef.TopLevelDecls.ForEach(Visit);
          return;
        }
        path.Add(d.Name);
        info.ToImport.Add(string.Join(".", path));
        d.ModuleDef.TopLevelDecls.ForEach(Visit);
        path.RemoveAt(path.Count - 1);
      }

      private void Visit(IndDatatypeDecl d) {
        path.Add(d.Name);
        d.Members.ForEach(Visit);
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
        var returnTypes = m.Outs.Select(arg => arg.Type.ToString()).ToList();
        info.returnTypes[methodName] = returnTypes;
      }

      private new void Visit(Function f) {
        var methodName = f.Name;
        if (path.Count != 0) {
          methodName = $"{string.Join(".", path)}.{methodName}";
        }
        if (f.HasStaticKeyword || !insideAClass) {
          info.isStatic.Add(methodName);
        }
        var returnTypes = new List<string> { f.ResultType.ToString() };
        info.returnTypes[methodName] = returnTypes;
      }
    }
  }
}