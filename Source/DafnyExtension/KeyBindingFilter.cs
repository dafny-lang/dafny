using System;
using System.ComponentModel.Composition;
using EnvDTE;
using Microsoft.VisualStudio;
using Microsoft.VisualStudio.OLE.Interop;
using Microsoft.VisualStudio.Utilities;
using Microsoft.VisualStudio.Editor;
using Microsoft.VisualStudio.Text.Editor;
using Microsoft.VisualStudio.TextManager.Interop;
using Microsoft.VisualStudio.Shell;
using Microsoft.VisualStudio.Shell.Interop;

namespace DafnyLanguage
{
  internal class KeyBindingCommandFilter : IOleCommandTarget
  {
    private IWpfTextView m_textView;
    internal IOleCommandTarget m_nextTarget;
    internal bool m_added;

    [Import(typeof(Microsoft.VisualStudio.Shell.SVsServiceProvider))]
    internal System.IServiceProvider _serviceProvider = null;

    public KeyBindingCommandFilter(IWpfTextView textView) {
      m_textView = textView;
    }


    public int QueryStatus(ref Guid pguidCmdGroup, uint cCmds, OLECMD[] prgCmds, IntPtr pCmdText) {
      if (pguidCmdGroup == typeof(VSConstants.VSStd97CmdID).GUID) {
        if (cCmds == 1) {
          switch (prgCmds[0].cmdID) {
            case (uint)VSConstants.VSStd97CmdID.GotoDefn: // F12
            case (uint)VSConstants.VSStd97CmdID.Start:    // F5
            case (uint)VSConstants.VSStd97CmdID.StepInto: // F11 
              prgCmds[0].cmdf = (uint) OLECMDF.OLECMDF_SUPPORTED;
              prgCmds[0].cmdf |= (uint)OLECMDF.OLECMDF_ENABLED;
              return VSConstants.S_OK;
          }
        }
      }
      return m_nextTarget.QueryStatus(ref pguidCmdGroup, cCmds, prgCmds, pCmdText);
    }

    public int Exec(ref Guid pguidCmdGroup, uint nCmdID, uint nCmdexecopt, IntPtr pvaIn, IntPtr pvaOut) {
      if (pguidCmdGroup == typeof(VSConstants.VSStd97CmdID).GUID) {
        switch (nCmdID) {
          case (uint)VSConstants.VSStd97CmdID.Start:    // F5
            if (DafnyClassifier.DafnyMenuPackage.MenuProxy.StopVerifierCommandEnabled(m_textView)) {
              DafnyClassifier.DafnyMenuPackage.MenuProxy.StopVerifier(m_textView);
            } else {
              DafnyClassifier.DafnyMenuPackage.MenuProxy.RunVerifier(m_textView);
            }
            return VSConstants.S_OK;
          case (uint)VSConstants.VSStd97CmdID.StepInto:
            if (DafnyClassifier.DafnyMenuPackage.MenuProxy.StopResolverCommandEnabled(m_textView)) {
              DafnyClassifier.DafnyMenuPackage.MenuProxy.StopResolver(m_textView);
            } else {
              DafnyClassifier.DafnyMenuPackage.MenuProxy.RunResolver(m_textView);
            }
            return VSConstants.S_OK;
          case (uint)VSConstants.VSStd97CmdID.GotoDefn: // F12
            DafnyClassifier.DafnyMenuPackage.MenuProxy.GoToDefinition(m_textView);
            return VSConstants.S_OK;
        }
      }

      return m_nextTarget.Exec(pguidCmdGroup, nCmdID, nCmdexecopt, pvaIn, pvaOut);
    }
  }

  [Export(typeof(IVsTextViewCreationListener))]
  [ContentType("dafny")]
  [TextViewRole(PredefinedTextViewRoles.Editable)]
  internal class KeyBindingCommandFilterProvider : IVsTextViewCreationListener {

    [Import(typeof(IVsEditorAdaptersFactoryService))]
    internal IVsEditorAdaptersFactoryService editorFactory = null;
    Events events;
    EnvDTE.DocumentEvents documentEvents;


    public void VsTextViewCreated(IVsTextView textViewAdapter) {
      IWpfTextView textView = editorFactory.GetWpfTextView(textViewAdapter);
      if (textView == null)
        return;

      AddCommandFilter(textViewAdapter, new KeyBindingCommandFilter(textView));

      // add Document saved event
      DTE dte = (DTE)ServiceProvider.GlobalProvider.GetService(typeof(DTE));
      events = (Events)dte.Events;
      documentEvents = events.DocumentEvents;
      documentEvents.DocumentSaved += DocumentSaved;
    }

    private void DocumentSaved(EnvDTE.Document document) {
      DafnyLanguage.ProgressTagger tagger;
      IWpfTextView textView = GetWpfTextView(document.FullName);
      if (textView != null && DafnyLanguage.ProgressTagger.ProgressTaggers.TryGetValue(textView.TextBuffer, out tagger)) {
        MenuProxy.Output("restart verifier on file save: " + document.FullName + "\n");
        // stop the old verification
        tagger.StopVerification();

        // start a new one.
        tagger.StartVerification(false);
      }
    }

    private IWpfTextView GetWpfTextView(string filePath) {
      DTE dte = (DTE)ServiceProvider.GlobalProvider.GetService(typeof(DTE));
      Microsoft.VisualStudio.OLE.Interop.IServiceProvider provider = (Microsoft.VisualStudio.OLE.Interop.IServiceProvider)dte;
      ServiceProvider serviceProvider = new ServiceProvider(provider);

      IVsUIHierarchy uiHierarchy;
      uint itemID;
      IVsWindowFrame windowFrame;
      
      if (Microsoft.VisualStudio.Shell.VsShellUtilities.IsDocumentOpen(serviceProvider, filePath, Guid.Empty,
                                      out uiHierarchy, out itemID, out windowFrame)) {
        // Get the IVsTextView from the windowFrame.
        IVsTextView textView =  Microsoft.VisualStudio.Shell.VsShellUtilities.GetTextView(windowFrame);
        return editorFactory.GetWpfTextView(textView);
      }

      return null;
    }


    void AddCommandFilter(IVsTextView viewAdapter, KeyBindingCommandFilter commandFilter) {
      if (commandFilter.m_added == false) {
        //get the view adapter from the editor factory
        IOleCommandTarget next;
        int hr = viewAdapter.AddCommandFilter(commandFilter, out next);

        if (hr == VSConstants.S_OK) {
          commandFilter.m_added = true;
          //you'll need the next target for Exec and QueryStatus 
          if (next != null)
            commandFilter.m_nextTarget = next;
        }
      }
    }

  }
}
