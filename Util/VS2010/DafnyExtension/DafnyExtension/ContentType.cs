using System.ComponentModel.Composition;
using Microsoft.VisualStudio.Utilities;

namespace DafnyLanguage
{
  class DafnyContentType
  {
    [Export]
    [Name("dafny")]
    [BaseDefinition("code")]
    internal static ContentTypeDefinition ContentType = null;

    [Export]
    [FileExtension(".dfy")]
    [ContentType("dafny")]
    internal static FileExtensionToContentTypeDefinition FileType = null;
  }
}
