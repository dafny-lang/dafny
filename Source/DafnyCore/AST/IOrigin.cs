#nullable enable
using System;
using System.IO;

namespace Microsoft.Dafny;

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
  string Filepath => Uri.LocalPath;

  Uri Uri { get; }

  TokenRange? EntireRange { get; }
  TokenRange ReportingRange {
    get;
  }

  Token Center => ReportingRange.Start;

  bool IsCopy { get; }
}