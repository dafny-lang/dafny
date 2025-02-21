#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using NJsonSchema.Annotations;

namespace Microsoft.Dafny;

public class FilesContainer(List<FileStart> files) {
  public List<FileStart> Files { get; } = files;
}

public class FileStart {
  public string Uri { get; }
  public List<TopLevelDecl> TopLevelDecls { get; }

  public FileStart(string uri, List<TopLevelDecl> topLevelDecls) {
    Uri = uri;
    TopLevelDecls = topLevelDecls;
  }
}

/// <summary>
/// This is a temporary container of everything declared at the top level of a file, including include directives.
/// After parsing, the contents of this 'module' are moved into the default module.
/// In the future, files may declare implicit modules and then this class will play a non-temporary role:
/// https://github.com/dafny-lang/dafny/issues/3027
/// </summary>
public class FileModuleDefinition : ModuleDefinition {
  public List<Include> Includes { get; } = [];

  public FileModuleDefinition(IOrigin origin) :
    base(origin, new Name("_module"), [],
      ModuleKindEnum.Concrete, false, null, null!, null) {
    {
    }
  }

  [SyntaxConstructor]
  public FileModuleDefinition(IOrigin origin, Name nameNode, List<IOrigin> prefixIds, ModuleKindEnum moduleKind,
    Implements? implements, ModuleDefinition enclosingModule, Attributes? attributes, List<TopLevelDecl> sourceDecls) :
    base(origin, nameNode, prefixIds, moduleKind, implements, enclosingModule, attributes, sourceDecls) {
  }

  public FileModuleDefinition(Cloner cloner, FileModuleDefinition original)
    : base(cloner, original) {
    Includes = original.Includes;
  }
}