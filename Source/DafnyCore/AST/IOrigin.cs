#nullable enable
using System;
using System.IO;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

class WithRange(IOrigin wrappedOrigin, TokenRange entireRange) : OriginWrapper(wrappedOrigin) {
  public override TokenRange EntireRange { get; } = entireRange;
}

public interface IOrigin : Boogie.IToken {

  bool IsInherited(ModuleDefinition m);
  bool IncludesRange { get; }
  /*
  int kind { get; set; }
  int pos { get; set; }
  int col { get; set; }
  int line { get; set; }
  string val { get; set; }
  bool IsValid { get; }*/

  string? Boogie.IToken.filename {
    get => Uri == null ? null : Path.GetFileName(Uri.LocalPath);
    set => throw new NotSupportedException();
  }

  public string? ActualFilename => Uri?.LocalPath;
  string Filepath => Uri?.LocalPath!;

  Uri Uri { get; }

  TokenRange? EntireRange { get; }
  TokenRange EntireRangeWithFallback => EntireRange ?? ReportingRange;

  TokenRange ReportingRange {
    get;
  }

  Token Center => ReportingRange.StartToken;

  bool IsCopy { get; }
}