using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Declaration = Microsoft.Boogie.Declaration;
using Function = Microsoft.Boogie.Function;
using IdentifierExpr = Microsoft.Boogie.IdentifierExpr;
using Program = Microsoft.Boogie.Program;
using TypeSynonymDecl = Microsoft.Boogie.TypeSynonymDecl;

namespace DafnyTestGeneration; 

public class BoogieMerger {

  public readonly Program Program;

  // Map the type of the declaration to a dictionary that, in turn,
  // maps the name to a list of declarations that originally had that name coupled with their current name
  private Dictionary<String, Dictionary<String, List<(String stringRepr, String name)>>> declarations;
  private HashSet<String> axioms;

  private Regex Indices = new Regex("#[0-9]+");

  /// <summary>
  /// Merge Boogie Programs by removing any duplicate top level declarations
  /// and resolving any name clashes
  /// </summary>
  public BoogieMerger(IEnumerable<Program> programs) {
    Program = new Program();
    declarations = new();
    axioms = new();
    int i = 0;
    var programNames = programs.Select(p => p.Procedures.Where(p => p.Name.Contains("$$") && p.Name.Split(".").Length >= 2)
     .Select(p => p.Name.Split("$$")[1].Split(".")[0]).First());
    foreach (var p in programs) {
      var programName = p.Procedures.Where(p => p.Name.Contains("$$") && p.Name.Split(".").Length >= 2)
        .Select(p => p.Name.Split("$$")[1].Split(".")[0]).First();
      /*if (!new List<string> {"Assumptions", "Cache", "Constant", "Engine", "PolicyEval", "PolicyUtil", "RequestContext", 
            "RequestType", "Spec", "SpecLemma", "Statement", "TypeConversion", "YuccaEvaluationResponse",
            "Condition", "ForAllValuesCheck", "ForAnyValueCheck", "ForSingleValueCheck"
          }.Contains(programName)) {
        continue;
      }*/
      // Balsa = "com_mamazon_mbalsa_mengine"
      // Yucca = "proto_mYucca", "proto_m_ProtobufDefaults", "protobuf"
      // JavaUtil = "java_mutil_mconcurrent_mTimeUnit_mNANOSECONDS", "java_mutil_mIterator", "java_mutil", 
      /*if (!new List<string> {"Engine", "Map", "Result", "TypeUtil", "YuccaRuntime", "Assumptions", 
             "Cache", "Constant", "PolicyEval", "PolicyUtil", "RequestContext", "RequestType", "TypeConversion",
             "YuccaEvaluationResponse", "com_mamazon_mbalsa_mengine", "proto_mYucca", "proto_mProtobufDefaults", 
             "protobuf", "java_mutil_mconcurrent_mTimeUnit_mNANOSECONDS", "java_mutil_mIterator", "java_mutil"
           }.Contains(programName)) {
        continue;
      }*/
      /*if (!new List<string> {"Engine", "PolicyEval"}.Contains(programName)) {
        continue;
      }*/
      /*if (!new List<string> {"Statement"}.Contains(programName)) {
        continue;
      }*/
      Console.WriteLine(i++ + " out of " + programs.Count() + " (" + p.TopLevelDeclarations.Count + " declarations, name=" + programName + ")");
      p.Resolve(DafnyOptions.O);
      p.Typecheck(DafnyOptions.O);
      var nameChanges = new Dictionary<String, Dictionary<String, String>>();
      var toRemove = new List<Declaration>();
      foreach (var topLevelDeclaration in p.TopLevelDeclarations) {

        if (topLevelDeclaration is not NamedDeclaration declaration) {
          continue;
        }
        var typeName = declaration.GetType().Name;
        if (!nameChanges.ContainsKey(typeName)) {
          nameChanges[typeName] = new();
        }

        var existing = GetSameNameDeclarations(declaration);
        if (existing.Count == 0) {
          existing.Add((GetStringRepresentation(declaration), declaration.Name));
          continue;
        }


        // TODO: Code below is problematic 
        /*if (declaration.Name.Contains("$$") && declaration.Name.Split(".").Length >= 2) {
          toRemove.Add(declaration);
          continue;
        } */
        // End of problematic code

        var foundEqual = false;
        foreach (var d in existing) {
          if (d.stringRepr == GetStringRepresentation(declaration)) {
            if (declaration.Name != d.name) {
              nameChanges[typeName][declaration.Name] = d.name;
            }
            toRemove.Add(declaration);
            foundEqual = true;
            break;
          }
        }

        if (foundEqual) {
          continue;
        }

        var newName = GetNewName(declaration);
        nameChanges[typeName][declaration.Name] = newName;
        existing.Add((GetStringRepresentation(declaration), newName));
      }
      new AddPrefixVisitor(nameChanges).Visit(p);
      p.Resolve(DafnyOptions.O);

      foreach (var topLevelDeclaration in p.TopLevelDeclarations) {
        if (topLevelDeclaration is not NamedDeclaration) {
          var stringRepr = GetStringRepresentation(topLevelDeclaration);
          if (axioms.Contains(stringRepr)) {
            toRemove.Add(topLevelDeclaration);
          } else {
            axioms.Add(stringRepr);
          }
        }
      }

      toRemove.ForEach(d => p.RemoveTopLevelDeclaration(d));
      Program.AddTopLevelDeclarations(p.TopLevelDeclarations);
      Program = Utils.DeepCloneProgram(Program);
      Program.Resolve(DafnyOptions.O);
      Program.Typecheck(DafnyOptions.O);
    }
  }

  private String GetNewName(NamedDeclaration declaration) {
    var existing = GetSameNameDeclarations(declaration);
    int i = 0;
    while (existing.Exists(p => p.name == declaration.Name + "_id" + i)) {
      i++;
    }
    return declaration.Name + "_id" + i;
  }

  private string GetStringRepresentation(Declaration declaration) {
    var output = new StringWriter();
    declaration.Emit(new TokenTextWriter(output, DafnyOptions.O), 0);
    return Indices.Replace(output.ToString(), "");
  }

  public static string GetStringRepresentation2(Program program) {
    var oldPrintInstrumented = DafnyOptions.O.PrintInstrumented;
    var oldPrintFile = DafnyOptions.O.PrintFile;
    DafnyOptions.O.PrintInstrumented = true;
    DafnyOptions.O.PrintFile = "-";
    var output = new StringWriter();
    program.Emit(new TokenTextWriter(output, DafnyOptions.O));
    DafnyOptions.O.PrintInstrumented = oldPrintInstrumented;
    DafnyOptions.O.PrintFile = oldPrintFile;
    return output.ToString();
  }

  private List<(String stringRepr, String name)> GetSameNameDeclarations(NamedDeclaration declaration) {
    var typeName = declaration.GetType().Name;
    if (!declarations.ContainsKey(typeName)) {
      declarations[typeName] = new();
    }
    if (!declarations[typeName].ContainsKey(declaration.Name)) {
      declarations[typeName][declaration.Name] = new();
    }
    return declarations[typeName][declaration.Name];
  }


  class AddPrefixVisitor : ReadOnlyVisitor {
    private Dictionary<String, Dictionary<String, String>> nameChanges;

    class MyHashSet {
      HashSet<int> hs = new();
      public bool Contains(Absy absy) {
        // return absy != null && hs.Contains(absy.UniqueId);
        return hs.Contains(absy.UniqueId);
      }

      public void Add(Absy absy) {
        /*if (absy == null) {
        return node;
        }*/
        hs.Add(absy.UniqueId);
      }
    }
    MyHashSet visited = new MyHashSet();
    HashSet<Declaration> global_decls = new HashSet<Declaration>();
    List<Function> functions = new List<Function>();

    public AddPrefixVisitor(Dictionary<String, Dictionary<String, String>> nameChanges) {
      this.nameChanges = nameChanges;
    }

    string AddPrefix(string typeName, string name) {
      return nameChanges.GetValueOrDefault(typeName, new())
        .GetValueOrDefault(name, name);
    }
    void Rename(NamedDeclaration node) {
      /*if (node == null) {
        return node;
      }*/
      node.Name = AddPrefix(node.GetType().Name, node.Name);
    }

    public override Program VisitProgram(Program node) {
      if (visited.Contains(node)) { return node; }
      visited.Add(node);
      global_decls.UnionWith(node.TopLevelDeclarations);
      functions.AddRange(node.Functions);
      return base.VisitProgram(node);
    }

    public override Procedure VisitProcedure(Procedure node) {
      /*if (node == null) {
        return node;
      }*/
      if (visited.Contains(node)) { return node; }
      visited.Add(node);
      Rename(node);
      return base.VisitProcedure(node);
    }

    public override Implementation VisitImplementation(Implementation node) {
      /*if (node == null) {
        return node;
      }*/
      if (visited.Contains(node)) { return node; }
      visited.Add(node);
      Rename(node);
      return base.VisitImplementation(node);
    }

    public override GlobalVariable VisitGlobalVariable(GlobalVariable node) {
      /*if (node == null) {
        return node;
      }*/
      if (visited.Contains(node)) { return node; }
      visited.Add(node);
      Rename(node);
      var candidateName = AddPrefix("TypeCtorDecl", node.TypedIdent.Name);
      if (candidateName == node.TypedIdent.Name) {
        candidateName = AddPrefix("TypeSynonymDecl", node.TypedIdent.Name);
      }
      node.TypedIdent.Name = candidateName;
      return base.VisitGlobalVariable(node);
    }

    public override Constant VisitConstant(Constant node) {
      /*if (node == null) {
        return node;
      }*/
      if (visited.Contains(node)) { return node; }
      visited.Add(node);
      Rename(node);
      var candidateName = AddPrefix("TypeCtorDecl", node.TypedIdent.Name);
      if (candidateName == node.TypedIdent.Name) {
        candidateName = AddPrefix("TypeSynonymDecl", node.TypedIdent.Name);
      }
      node.TypedIdent.Name = candidateName;
      return base.VisitConstant(node);
    }

    public override Expr VisitIdentifierExpr(IdentifierExpr node) {
      /*if (node == null) {
        return node;
      }*/
      if (visited.Contains(node)) { return node; }
      visited.Add(node);
      // Needs to be visited before setting the new name
      //if (node.Decl != null) {
      Visit(node.Decl);
      if (global_decls.Contains(node.Decl)) {
        node.Name = node.Decl.Name;
      }
      //}
      return base.VisitIdentifierExpr(node);
    }

    public override TypedIdent VisitTypedIdent(TypedIdent node) {
      /*if (node == null) {
        return node;
      }*/
      node = base.VisitTypedIdent(node);
      // The ReadOnly Visitor doesn't visit where expressions by default
      if (node.WhereExpr != null) {
        node.WhereExpr = (Expr)Visit(node.WhereExpr);
      }
      return node;
    }

    public override Function VisitFunction(Function node) {
      /*if (node == null) {
        return node;
      }*/
      if (visited.Contains(node)) { return node; }
      visited.Add(node);
      Rename(node);
      return base.VisitFunction(node);
    }

    public override Expr VisitNAryExpr(NAryExpr node) {
      /*if (node == null) {
        return node;
      }*/
      if (visited.Contains(node)) { return node; }
      visited.Add(node);
      // We need to make sure a called function is visited before rewriting a call
      if (node.Fun is FunctionCall && !visited.Contains(((node.Fun as FunctionCall)!).Func)) {
        VisitFunction(((node.Fun as FunctionCall)!).Func);
      }

      var rep_fun = functions.Find(x => x.Name == AddPrefix("Function", node.Fun.FunctionName));
      if (rep_fun != null) {
        node.Fun = new FunctionCall(rep_fun);
      }
      return base.VisitNAryExpr(node);
    }

    public override Cmd VisitCallCmd(CallCmd node) {
      /*if (node == null) {
        return node;
      }*/
      if (visited.Contains(node)) { return node; }
      visited.Add(node);
      //if (node.Proc != null) {
      VisitProcedure(node.Proc);
      node.callee = node.Proc.Name;
      //}
      return base.VisitCallCmd(node);
    }

    public override Declaration VisitTypeCtorDecl(TypeCtorDecl node) {
      /*if (node == null) {
        return node;
      }*/
      if (visited.Contains(node)) { return node; }
      visited.Add(node);
      Rename(node);
      return base.VisitTypeCtorDecl(node);
    }

    public override Declaration VisitTypeSynonymDecl(TypeSynonymDecl node) {
      /*if (node == null) {
        return node;
      }*/
      if (visited.Contains(node)) { return node; }
      visited.Add(node);
      Rename(node);
      return base.VisitTypeSynonymDecl(node);
    }
  }
}