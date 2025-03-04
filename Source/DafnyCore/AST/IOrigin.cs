using System;
using System.IO;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public interface IOrigin : Boogie.IToken {

  bool IsInherited(ModuleDefinition m);

  int Length => EndToken.pos - StartToken.pos;

  bool InclusiveEnd { get; }
  bool IncludesRange { get; }
  /*
  int kind { get; set; }
  int pos { get; set; }
  int col { get; set; }
  int line { get; set; }
  string val { get; set; }
  bool IsValid { get; }*/

  string Boogie.IToken.filename {
    get => Uri == null ? null : Path.GetFileName(Uri.LocalPath);
    set => throw new NotSupportedException();
  }

  public string ActualFilename => Uri.LocalPath;
  string Filepath => Uri?.LocalPath;

  Uri Uri { get; }

  Token StartToken { get; }
  Token EndToken { get; }
  Location Center { get; }

  bool IsCopy { get; }
}