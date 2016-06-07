using System;
using System.Runtime.InteropServices;
using System.Collections.Generic;
using System.ComponentModel.Composition;
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


    public void VsTextViewCreated(IVsTextView textViewAdapter) {
      IWpfTextView textView = editorFactory.GetWpfTextView(textViewAdapter);
      if (textView == null)
        return;

      AddCommandFilter(textViewAdapter, new KeyBindingCommandFilter(textView));
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
