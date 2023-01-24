//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.IO;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Collections.ObjectModel;
using JetBrains.Annotations;
using Microsoft.BaseTypes;


namespace Microsoft.Dafny.Compilers {
  internal class InternalCompilersPluginConfiguration : Plugins.PluginConfiguration {
    public static readonly InternalCompilersPluginConfiguration Singleton = new();

    public override Plugins.Compiler[] GetCompilers() {
      return new Plugins.Compiler[] {
        new Compilers.CsharpCompiler(),
        new Compilers.JavaScriptCompiler(),
        new Compilers.GoCompiler(),
        new Compilers.JavaCompiler(),
        new Compilers.PythonCompiler(),
        new Compilers.CppCompiler()
      };
    }
  }

  public abstract class SinglePassCompiler<TExpression> : Plugins.Compiler
    where TExpression : ICanRender {

    protected internal abstract TExpression TrExpr(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wStmts);
    protected abstract TExpression EmitThis();

    protected abstract TExpression EmitLiteralExpr(LiteralExpr e);
    protected delegate TExpression FCE_Arg_Translator(Expression e, bool inLetExpr, ConcreteSyntaxTree wStmts);

    public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string/*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
      bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {
      Contract.Requires(dafnyProgramName != null);
      Contract.Requires(targetProgramText != null);
      Contract.Requires(otherFileNames != null);
      Contract.Requires(otherFileNames.Count == 0 || targetFilename != null);
      Contract.Requires(this.SupportsInMemoryCompilation || targetFilename != null);
      Contract.Requires(!runAfterCompile || callToMain != null);
      Contract.Requires(outputWriter != null);

      compilationResult = null;
      return true;
    }

    public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string/*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
      object compilationResult, TextWriter outputWriter) {
      Contract.Requires(dafnyProgramName != null);
      Contract.Requires(targetProgramText != null);
      Contract.Requires(otherFileNames != null);
      Contract.Requires(otherFileNames.Count == 0 || targetFilename != null);
      Contract.Requires(outputWriter != null);
      return true;
    }
  }
}
