using System;
using System.Collections.Generic;
using DafnyCore.Options;

namespace Microsoft.Dafny;

public class CompilationData(
  ErrorReporter errorReporter,
  List<Include> includes,
  IList<Uri> rootSourceUris,
  ISet<Uri> alreadyVerifiedRoots,
  ISet<Uri> alreadyCompiledRoots) {
  public DafnyOptions Options => ErrorReporter.Options;
  public ErrorReporter ErrorReporter { get; } = errorReporter;
  public IList<Uri> RootSourceUris { get; } = rootSourceUris;

  public ISet<Uri> AlreadyVerifiedRoots { get; } = alreadyVerifiedRoots;
  public ISet<Uri> AlreadyCompiledRoots { get; } = alreadyCompiledRoots;

  public List<Include> Includes = includes;
  // TODO move to DocumentAfterParsing once that's used by the CLI
  [FilledInDuringResolution]
  public ISet<Uri> UrisToVerify;
  // TODO move to DocumentAfterParsing once that's used by the CLI
  [FilledInDuringResolution]
  public ISet<Uri> UrisToCompile;

  public TranslationRecord AlreadyTranslatedRecord { get; set; }
}