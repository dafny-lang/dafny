using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class CompilationAfterParsing : CompilationInput {

  public CompilationAfterParsing(CompilationInput compilation, Program program)
    : base(compilation.Options, compilation.Version, compilation.Project, compilation.RootUris) {
    Program = program;
  }

  public Program Program { get; }
}