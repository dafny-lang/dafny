using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.VisualStudio.Text.Editor;
using Microsoft.VisualStudio.Shell;
using Microsoft.VisualStudio.Shell.Interop;

namespace DafnyLanguage
{
  class MenuProxy : DafnyLanguage.DafnyMenu.IMenuProxy
  {
    private DafnyMenu.DafnyMenuPackage DafnyMenuPackage;

    public MenuProxy(DafnyMenu.DafnyMenuPackage DafnyMenuPackage)
    {
      this.DafnyMenuPackage = DafnyMenuPackage;
    }

    public int ToggleSnapshotVerification(IWpfTextView activeTextView)
    {
      return DafnyDriver.ChangeIncrementalVerification(1);
    }

    public int ToggleMoreAdvancedSnapshotVerification(IWpfTextView activeTextView)
    {
      return DafnyDriver.ChangeIncrementalVerification(2);
    }

    public bool MoreAdvancedSnapshotVerificationCommandEnabled(IWpfTextView activeTextView)
    {
      return activeTextView != null
             && 0 < DafnyDriver.IncrementalVerificationMode();
    }

    public bool ToggleAutomaticInduction(IWpfTextView activeTextView) {
      return DafnyDriver.ChangeAutomaticInduction();
    }

    public bool AutomaticInductionCommandEnabled(IWpfTextView activeTextView) {
      return activeTextView != null;
    }

    public bool StopVerifierCommandEnabled(IWpfTextView activeTextView)
    {
      DafnyLanguage.ProgressTagger tagger;
      return activeTextView != null
                    && StopResolverCommandEnabled(activeTextView) // verifier can start/stop only when resolver is running.
                    && DafnyLanguage.ProgressTagger.ProgressTaggers.TryGetValue(activeTextView.TextBuffer, out tagger)
                    && tagger != null && !tagger.VerificationDisabled;
    }

    public void StopVerifier(IWpfTextView activeTextView)
    {
      DafnyLanguage.ProgressTagger tagger;
      if (activeTextView != null && DafnyLanguage.ProgressTagger.ProgressTaggers.TryGetValue(activeTextView.TextBuffer, out tagger))
      {
        MenuProxy.Output("verifier manually stopped\n");
        tagger.StopVerification();
      }
    }

    public bool RunVerifierCommandEnabled(IWpfTextView activeTextView)
    {
      DafnyLanguage.ProgressTagger tagger;
      return activeTextView != null
                 && StopResolverCommandEnabled(activeTextView) // verifier can start/stop only when resolver is running.       
                 && DafnyLanguage.ProgressTagger.ProgressTaggers.TryGetValue(activeTextView.TextBuffer, out tagger)
                 && tagger != null && tagger.VerificationDisabled;
    }

    public void RunVerifier(IWpfTextView activeTextView)
    {
      DafnyLanguage.ProgressTagger tagger;
      if (activeTextView != null && DafnyLanguage.ProgressTagger.ProgressTaggers.TryGetValue(activeTextView.TextBuffer, out tagger))
      {
        MenuProxy.Output("verifier manually started\n");
        tagger.StartVerification(false);
      }
    }

    public bool StopResolverCommandEnabled(IWpfTextView activeTextView) {
      DafnyLanguage.ResolverTagger resolver;
      return activeTextView != null
                    && DafnyLanguage.ResolverTagger.ResolverTaggers.TryGetValue(activeTextView.TextBuffer, out resolver)
                    && resolver != null && resolver.RunResolver;
    }

    public void StopResolver(IWpfTextView activeTextView) {
      DafnyLanguage.ResolverTagger resolver;
      if (activeTextView != null && DafnyLanguage.ResolverTagger.ResolverTaggers.TryGetValue(activeTextView.TextBuffer, out resolver)) {
        MenuProxy.Output("resolver and verifier manually stopped\n");
        resolver.RunResolver = false;
        resolver.Program = null;
      }
      DafnyLanguage.ProgressTagger tagger;
      if (activeTextView != null && DafnyLanguage.ProgressTagger.ProgressTaggers.TryGetValue(activeTextView.TextBuffer, out tagger)) {
        tagger.StartVerification(false);
      }
    }

    public bool RunResolverCommandEnabled(IWpfTextView activeTextView) {
      DafnyLanguage.ResolverTagger resolver;
      return activeTextView != null
                 && DafnyLanguage.ResolverTagger.ResolverTaggers.TryGetValue(activeTextView.TextBuffer, out resolver)
                 && resolver != null && !resolver.RunResolver;
    }

    public void RunResolver(IWpfTextView activeTextView) {
      DafnyLanguage.ResolverTagger resolver;
      if (activeTextView != null && DafnyLanguage.ResolverTagger.ResolverTaggers.TryGetValue(activeTextView.TextBuffer, out resolver)) {
        MenuProxy.Output("resolver and verifier manually started\n");
        resolver.RunResolver = true;
        resolver.ResolveBuffer(null, null);
      }
      DafnyLanguage.ProgressTagger tagger;
      if (activeTextView != null && DafnyLanguage.ProgressTagger.ProgressTaggers.TryGetValue(activeTextView.TextBuffer, out tagger)) {
        tagger.StartVerification(false);
      }
    }

    public void DiagnoseTimeouts(IWpfTextView activeTextView)
    {
      DafnyLanguage.ProgressTagger tagger;
      if (activeTextView != null && DafnyLanguage.ProgressTagger.ProgressTaggers.TryGetValue(activeTextView.TextBuffer, out tagger))
      {
        tagger.StartVerification(false, true);
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

    public bool DiagnoseTimeoutsCommandEnabled(IWpfTextView activeTextView)
    {
      ResolverTagger resolver;
      return activeTextView != null
                    && DafnyLanguage.ResolverTagger.ResolverTaggers.TryGetValue(activeTextView.TextBuffer, out resolver)
                    && resolver.VerificationErrors.Any(err => err.Message.Contains("timed out"));
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

    public void GoToDefinition(IWpfTextView activeTextView) {
      int caretPos = activeTextView.Caret.Position.BufferPosition.Position;
      string fileName;
      int lineNumber;
      int offset;
      DafnyLanguage.IdentifierTagger tagger;
      if (activeTextView != null && DafnyLanguage.IdentifierTagger.IdentifierTaggers.TryGetValue(activeTextView.TextBuffer, out tagger)) {
        if (tagger.FindDefinition(caretPos, out fileName, out lineNumber, out offset)) {
          DafnyMenuPackage.GoToDefinition(fileName, lineNumber, offset);
        }
      }
    }

    public static void Output(string msg) {
      // Get the output window
      var outputWindow = Package.GetGlobalService(typeof(SVsOutputWindow)) as IVsOutputWindow;

      // Ensure that the desired pane is visible
      var paneGuid = Microsoft.VisualStudio.VSConstants.OutputWindowPaneGuid.GeneralPane_guid;
      IVsOutputWindowPane pane;
      outputWindow.CreatePane(paneGuid, "Dafny", 1, 0);
      outputWindow.GetPane(paneGuid, out pane);

      // Output the message
      pane.OutputString(msg);
    }
  }
}
