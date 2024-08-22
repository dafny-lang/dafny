using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reactive;

namespace Microsoft.Dafny.Compilers;

public class VerifiedJavaBackend : JavaBackend {

  public override string TargetId => "vjava";
  
  public override void Compile(Program dafnyProgram, string dafnyProgramName, ConcreteSyntaxTree output) {

    CodeGenerator.Compile(dafnyProgram, output);
  }
  
  protected override CodeGenerator CreateCodeGenerator() {
    return new VerifiedJavaCodeGenerator();
  }
  
  class VerifiedJavaCodeGenerator : CodeGenerator {
    public string ModuleSeparator { get; }
    public CoverageInstrumenter Coverage { get; }
    public IReadOnlySet<Feature> UnsupportedFeatures { get; }
    public bool SupportsDatatypeWrapperErasure { get; }

    public void Compile(Program dafnyProgram, ConcreteSyntaxTree output) {
      var fileModuleDefinition = new FileModuleDefinition(Token.NoToken);
      
      var parsed = false;
      Program programToCompile;
      if (parsed) {
        programToCompile = dafnyProgram.AfterParsing;
      } else {
        programToCompile = dafnyProgram;
      }
      RemoveGhost(programToCompile);
        
      fileModuleDefinition.SourceDecls.AddRange(
        programToCompile.DefaultModuleDef.SourceDecls.Where(td => !td.IsExtern(programToCompile.Options)));
      
      var grammar = new JavaGrammar(dafnyProgram.GetStartOfFirstFileToken().Uri, dafnyProgram.Options).GetFinalGrammar();
      var outputStringWriter = new StringWriter();
      grammar.ToPrinter().Print(fileModuleDefinition).ForceSuccess.Render(outputStringWriter);
      output.Write(outputStringWriter.ToString());
    }

    public string PublicIdProtect(string name) {
      throw new NotImplementedException();
    }

    public void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree callToMainTree) {
    }
  }

  static void RemoveGhost(Program program) {
    var visitor = new RemoveGhostVisitor();

    IEnumerable<ModuleDefinition> GetDefs(ModuleDefinition def) {
      return def.TopLevelDecls.OfType<ModuleDecl>().SelectMany(m => {
        if (m is LiteralModuleDecl literalModuleDecl) {
          return GetDefs(literalModuleDecl.ModuleDef);
        }

        return [];
      }).Concat([def]);
    }
    var modules = GetDefs(program.DefaultModuleDef);
    foreach (var module in modules) {
      if (!module.ShouldCompile(program.Compilation)) {
        continue;
      }
      
      foreach (var withMembers in module.TopLevelDecls.OfType<TopLevelDeclWithMembers>()) {
        foreach (var member in withMembers.Members.OfType<MethodOrFunction>()) {
          if (member is Method method) {
            visitor.Visit(method, Unit.Default);
          }

          if (member is Function function) {
            visitor.Visit(function, Unit.Default);
          }
        }
      }
    }
  }

  class RemoveGhostVisitor : TopDownVisitor<Unit> {
    
    public override void Visit(Method method, Unit st) {
      method.Req.Clear();
      method.Ens.Clear();
      method.Decreases.Expressions.Clear();
      method.Reads.Expressions.Clear();
      method.Mod.Expressions.Clear();
      base.Visit(method, st);
    }

    public override void Visit(Function function, Unit st) {
      function.Req.Clear();
      function.Reads.Expressions.Clear();
      function.Ens.Clear();
      base.Visit(function, st);
    }

    protected override bool VisitOneStmt(Statement stmt, ref Unit st) {
      if (stmt is BlockStmt blockStmt) {
        blockStmt.Body = blockStmt.Body.Where(s => {
          var isGhost = s.IsGhost;
          return !isGhost;
        }).ToList();
      }

      if (stmt is LoopStmt loopStmt) {
        loopStmt.Decreases.Expressions.Clear();
        loopStmt.Invariants.Clear();
      }
      return base.VisitOneStmt(stmt, ref st);
    }
  }

  public VerifiedJavaBackend(DafnyOptions options) : base(options) {
  }
}
