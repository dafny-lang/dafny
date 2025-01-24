using System;
using System.Collections.Generic;
using DafnyCore.Options;

namespace Microsoft.Dafny;

public record CompilationData(
  ErrorReporter ErrorReporter,
  List<Include> Includes,
  IList<Uri> RootSourceUris,
  ISet<Uri> AlreadyVerifiedRoots,
  ISet<Uri> AlreadyCompiledRoots) {

  public DafnyOptions Options => ErrorReporter.Options;
  public ErrorReporter ErrorReporter { get; } = ErrorReporter;
  public IList<Uri> RootSourceUris { get; } = RootSourceUris;

  public ISet<Uri> AlreadyVerifiedRoots { get; } = AlreadyVerifiedRoots;
  public ISet<Uri> AlreadyCompiledRoots { get; } = AlreadyCompiledRoots;

  public List<Include> Includes = Includes;
  // TODO move to DocumentAfterParsing once that's used by the CLI
  [FilledInDuringResolution]
  public ISet<Uri> UrisToVerify;
  // TODO move to DocumentAfterParsing once that's used by the CLI
  [FilledInDuringResolution]
  public ISet<Uri> UrisToCompile;

  public TranslationRecord AlreadyTranslatedRecord { get; set; }
}