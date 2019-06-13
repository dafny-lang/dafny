using System;
using System.Collections;
using System.ComponentModel;
using System.Drawing;
using System.Data;
using System.Windows;
using System.Runtime.InteropServices;
using Microsoft.VisualStudio.Shell.Interop;
using Microsoft.VisualStudio.Shell;

namespace DafnyLanguage.DafnyMenu
{
  /// <summary>
  /// This class implements the tool window exposed by this package and hosts a user control.
  ///
  /// In Visual Studio tool windows are composed of a frame (implemented by the shell) and a pane,
  /// usually implemented by the package implementer.
  ///
  /// This class derives from the ToolWindowPane class provided from the MPF in order to use its
  /// implementation of the IVsUIElementPane interface.
  /// </summary>
  [Guid(GuidList.guidToolWindowPersistanceString)]
  public class BvdToolWindow : ToolWindowPane
  {
    private static readonly Lazy<Microsoft.Boogie.ModelViewer.Main> bvdInstance = new Lazy<Microsoft.Boogie.ModelViewer.Main>(() => new Microsoft.Boogie.ModelViewer.Main(new string[] { }, true));

    /// <summary>
    /// Standard constructor for the tool window.
    /// </summary>
    public BvdToolWindow() :
      base(null)
    {
      // Set the window title reading it from the resources.
      this.Caption = "Verification Debugger";
      // Set the image that will appear on the tab of the window frame
      // when docked with an other window
      // The resource ID correspond to the one defined in the resx file
      // while the Index is the offset in the bitmap strip. Each image in
      // the strip being 16x16.
      // this.BitmapResourceID = 301;
      // this.BitmapIndex = 1;

      // This is the user control hosted by the tool window; Note that, even if this class implements IDisposable,
      // we are not calling Dispose on this object. This is because ToolWindowPane calls Dispose on
      // the object returned by the Content property.
      // base.Content = new MyControl();
    }

    public override System.Windows.Forms.IWin32Window Window
    {
      get { return bvdInstance.Value; }
    }

    public static Microsoft.Boogie.ModelViewer.Main BVD
    {
      get { return bvdInstance.Value; }
    }
  }
}
