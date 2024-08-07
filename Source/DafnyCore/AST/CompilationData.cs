using System;
using System.Collections.Generic;
using DafnyCore.Options;

namespace Microsoft.Dafny;

public class CompilationData {
  public CompilationData(ErrorReporter errorReporter, List<Include> includes, IList<Uri> rootSourceUris, ISet<Uri> alreadyVerifiedRoots, ISet<Uri> alreadyCompiledRoots) {
    Includes = includes;
    ErrorReporter = errorReporter;
    RootSourceUris = rootSourceUris;
    AlreadyVerifiedRoots = alreadyVerifiedRoots;
    AlreadyCompiledRoots = alreadyCompiledRoots;
  }

  public DafnyOptions Options => ErrorReporter.Options;
  public ErrorReporter ErrorReporter { get; }
  public IList<Uri> RootSourceUris { get; }

  public ISet<Uri> AlreadyVerifiedRoots { get; }
  public ISet<Uri> AlreadyCompiledRoots { get; }

  public List<Include> Includes;
  // TODO move to DocumentAfterParsing once that's used by the CLI
  [FilledInDuringResolution]
  public ISet<Uri> UrisToVerify;
  // TODO move to DocumentAfterParsing once that's used by the CLI
  [FilledInDuringResolution]
  public ISet<Uri> UrisToCompile;

  public TranslationRecord AlreadyTranslatedRecord { get; set; }
}