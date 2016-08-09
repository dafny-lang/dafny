using System.ComponentModel.Composition;
using Microsoft.VisualStudio.Text.Editor;
using Microsoft.VisualStudio.Utilities;


namespace DafnyLanguage
{
  class DafnyContentType
  {
    [Export]
    [Name("dafny")]
    [BaseDefinition("code")]
    internal static ContentTypeDefinition ContentType = null;

    [Export(typeof(IWpfTextViewCreationListener))]
    [ContentType("text")]
    [TextViewRole(PredefinedTextViewRoles.Document)]
    internal sealed class DafnyTextViewCreationListener : IWpfTextViewCreationListener
    {
      [Export(typeof(AdornmentLayerDefinition))]
      [Name("ModelAdornment")]
      [Order(After = PredefinedAdornmentLayers.Selection, Before = PredefinedAdornmentLayers.Text)]
      [TextViewRole(PredefinedTextViewRoles.Document)]
      public AdornmentLayerDefinition editorAdornmentLayer = null;
      public void TextViewCreated(IWpfTextView textView)
      {
      }
    }

    [Export]
    [FileExtension(".dfy")]
    [ContentType("dafny")]
    internal static FileExtensionToContentTypeDefinition FileType = null;
  }
}
