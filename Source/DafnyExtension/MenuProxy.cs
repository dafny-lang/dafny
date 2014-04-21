using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.VisualStudio.Text.Editor;

namespace DafnyLanguage
{
  class MenuProxy : DafnyLanguage.DafnyMenu.IMenuProxy
  {
    private DafnyMenu.DafnyMenuPackage DafnyMenuPackage;

    public MenuProxy(DafnyMenu.DafnyMenuPackage DafnyMenuPackage)
    {
      this.DafnyMenuPackage = DafnyMenuPackage;
    }

    public bool ToggleSnapshotVerification(IWpfTextView activeTextView)
    {
      return DafnyDriver.ToggleIncrementalVerification();
    }

    public bool StopVerifierCommandEnabled(IWpfTextView activeTextView)
    {
      DafnyLanguage.ProgressTagger tagger;
      return activeTextView != null
                    && DafnyLanguage.ProgressTagger.ProgressTaggers.TryGetValue(activeTextView.TextBuffer, out tagger)
                    && tagger != null && tagger.VerificationDisabled;
    }

    public void StopVerifier(IWpfTextView activeTextView)
    {
      DafnyLanguage.ProgressTagger tagger;
      if (activeTextView != null && DafnyLanguage.ProgressTagger.ProgressTaggers.TryGetValue(activeTextView.TextBuffer, out tagger))
      {
        tagger.StopVerification();
      }
    }

    public bool RunVerifierCommandEnabled(IWpfTextView activeTextView)
    {
      DafnyLanguage.ProgressTagger tagger;
      return activeTextView != null
                 && DafnyLanguage.ProgressTagger.ProgressTaggers.TryGetValue(activeTextView.TextBuffer, out tagger)
                 && tagger != null && tagger.VerificationDisabled;
    }

    public void RunVerifier(IWpfTextView activeTextView)
    {
      DafnyLanguage.ProgressTagger tagger;
      if (activeTextView != null && DafnyLanguage.ProgressTagger.ProgressTaggers.TryGetValue(activeTextView.TextBuffer, out tagger))
      {
        tagger.StartVerification();
      }
    }

    public bool MenuEnabled(IWpfTextView activeTextView)
    {
      return activeTextView != null && activeTextView.TextBuffer.ContentType.DisplayName == "dafny";
    }

    public bool CompileCommandEnabled(IWpfTextView activeTextView)
    {
      ResolverTagger resolver;
      return activeTextView != null
                    && DafnyLanguage.ResolverTagger.ResolverTaggers.TryGetValue(activeTextView.TextBuffer, out resolver)
                    && resolver.Program != null;
    }

    public void Compile(IWpfTextView activeTextView)
    {
      ResolverTagger resolver;
      if (activeTextView != null
          && DafnyLanguage.ResolverTagger.ResolverTaggers.TryGetValue(activeTextView.TextBuffer, out resolver)
          && resolver.Program != null)
      {
        var outputWriter = new StringWriter();
        DafnyMenuPackage.ExecuteAsCompiling(() => { DafnyDriver.Compile(resolver.Program, outputWriter); }, outputWriter);
      }
    }

    public bool ShowErrorModelCommandEnabled(IWpfTextView activeTextView)
    {
      ResolverTagger resolver;
      return activeTextView != null
                    && DafnyLanguage.ResolverTagger.ResolverTaggers.TryGetValue(activeTextView.TextBuffer, out resolver)
                    && resolver.Program != null
                    && resolver.VerificationErrors.Any(err => !string.IsNullOrEmpty(err.ModelText));
    }

    public void ShowErrorModel(IWpfTextView activeTextView)
    {
      ResolverTagger resolver = null;
      var show = activeTextView != null
                 && DafnyLanguage.ResolverTagger.ResolverTaggers.TryGetValue(activeTextView.TextBuffer, out resolver)
                 && resolver.Program != null
                 && resolver.VerificationErrors.Any(err => err.IsSelected && !string.IsNullOrEmpty(err.ModelText));
      if (show)
      {
        var selectedError = resolver.VerificationErrors.FirstOrDefault(err => err.IsSelected && !string.IsNullOrEmpty(err.ModelText));

        if (selectedError != null)
        {
          DafnyMenuPackage.ShowErrorModelInBVD(selectedError.ModelText, selectedError.SelectedStateId);
        }
      }
    }
  }
}
