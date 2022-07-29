using System;
using System.Collections.Generic;
using System.IO;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Program = Microsoft.Dafny.Program;
using Newtonsoft.Json;

namespace DafnyTestGeneration {
  class TargetPrinter {

    private DafnyInfo dafnyInfo;
    private Dictionary<string, int> targetedMethods = new();

    public TargetPrinter(DafnyInfo dafnyInfo) {
        this.dafnyInfo = dafnyInfo;
    }

    public MemberDecl? GetMethodOrFunctionFromName(string name) {
      foreach (var (funcName, func) in dafnyInfo.functions) {
        if (name.Equals(funcName))
          return func;
      }
      foreach (var (methodName, method) in dafnyInfo.methods) {
        if (name.Equals(methodName))
          return method;
      }
      return null;
    }

    public string GetFullDafnyNameFromImpl(Implementation impl) {
      int endOfName = impl.VerboseName.IndexOf(' ');
      return impl.VerboseName.Substring(0, endOfName);
    }

    public string GetFullCompiledName(MemberDecl decl) {
      var fullCompiledName = decl.CompileName;
      TopLevelDecl enclosingClass = decl.EnclosingClass;
      fullCompiledName = $"{enclosingClass.CompileName}.{fullCompiledName}";
      ModuleDefinition m = enclosingClass.EnclosingModuleDefinition;
      while (!m.IsDefaultModule) {
        if (Attributes.Contains(m.Attributes, "extern") && 
          Attributes.FindExpressions(m.Attributes, "extern").Count > 0) {
          fullCompiledName = $"{m.CompileName}.{fullCompiledName}";
        } else {
          fullCompiledName = $"{m.CompileName}_Compile.{fullCompiledName}";
        }

        m = m.EnclosingModule;
      }
      return fullCompiledName;
    }

    public void PopulateTargetedMethods(Dictionary<Implementation, int> testDict, bool passed) {
      foreach (var (impl, count) in testDict) {
        var fullDafnyName = GetFullDafnyNameFromImpl(impl);
        MemberDecl? decl = GetMethodOrFunctionFromName(fullDafnyName);
        if (decl == null)
          continue;
        var fullCompiledName = GetFullCompiledName(decl);
        if (passed || !targetedMethods.ContainsKey(fullCompiledName)) {
          targetedMethods.Add(fullCompiledName, passed ? count : 0);
        }
      }
    }

    public void WriteToFile(string filePath) {
      String json = JsonConvert.SerializeObject(targetedMethods, Newtonsoft.Json.Formatting.Indented);
      File.WriteAllText(filePath, json);
    }
  }
}