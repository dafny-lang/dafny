using System;
using System.Diagnostics;
using System.Globalization;
using System.Runtime.InteropServices;
using System.ComponentModel.Design;
using Microsoft.Win32;
using Microsoft.VisualStudio;
using Microsoft.VisualStudio.Shell.Interop;
using Microsoft.VisualStudio.OLE.Interop;
using Microsoft.VisualStudio.Shell;

namespace DafnyLanguage.DafnyMenu
{
  /// <summary>
  /// This is the class that implements the package exposed by this assembly.
  ///
  /// The minimum requirement for a class to be considered a valid package for Visual Studio
  /// is to implement the IVsPackage interface and register itself with the shell.
  /// This package uses the helper classes defined inside the Managed Package Framework (MPF)
  /// to do it: it derives from the Package class that provides the implementation of the 
  /// IVsPackage interface and uses the registration attributes defined in the framework to 
  /// register itself and its components with the shell.
  /// </summary>
  // This attribute tells the PkgDef creation utility (CreatePkgDef.exe) that this class is
  // a package.
  [PackageRegistration(UseManagedResourcesOnly = true)]
  // This attribute is used to register the information needed to show this package
  // in the Help/About dialog of Visual Studio.
  [InstalledProductRegistration("#110", "#112", "1.0", IconResourceID = 400)]
  // This attribute is needed to let the shell know that this package exposes some menus.
  [ProvideMenuResource("Menus.ctmenu", 1)]
  [ProvideAutoLoad("{6c7ed99a-206a-4937-9e08-b389de175f68}")]
  [Guid(GuidList.guidDafnyMenuPkgString)]
  public sealed class DafnyMenuPackage : Package
  {

    private OleMenuCommand compileCommand;
    private OleMenuCommand menuCommand;

    /// <summary>
    /// Default constructor of the package.
    /// Inside this method you can place any initialization code that does not require 
    /// any Visual Studio service because at this point the package object is created but 
    /// not sited yet inside Visual Studio environment. The place to do all the other 
    /// initialization is the Initialize method.
    /// </summary>
    public DafnyMenuPackage()
    {
      Debug.WriteLine(string.Format(CultureInfo.CurrentCulture, "Entering constructor for: {0}", this.ToString()));
    }


    #region Package Members

    /// <summary>
    /// Initialization of the package; this method is called right after the package is sited, so this is the place
    /// where you can put all the initialization code that rely on services provided by VisualStudio.
    /// </summary>
    protected override void Initialize()
    {
      Debug.WriteLine(string.Format(CultureInfo.CurrentCulture, "Entering Initialize() of: {0}", this.ToString()));
      base.Initialize();

      // Add our command handlers for menu (commands must exist in the .vsct file)
      var mcs = GetService(typeof(IMenuCommandService)) as OleMenuCommandService;
      if (null != mcs)
      {
        // Create the command for the menu item.
        var compileCommandID = new CommandID(GuidList.guidDafnyMenuCmdSet, (int)PkgCmdIDList.cmdidCompile);
        compileCommand = new OleMenuCommand(CompileCallback, compileCommandID);
        compileCommand.Enabled = false;
        compileCommand.BeforeQueryStatus += compileCommand_BeforeQueryStatus;
        mcs.AddCommand(compileCommand);

        var menuCommandID = new CommandID(GuidList.guidDafnyMenuPkgSet, (int)PkgCmdIDList.cmdidMenu);
        menuCommand = new OleMenuCommand(new EventHandler((sender, e) => { }), menuCommandID);
        menuCommand.BeforeQueryStatus += menuCommand_BeforeQueryStatus;
        menuCommand.Enabled = true;
        var s = menuCommand.OleStatus;
        mcs.AddCommand(menuCommand);
      }
    }

    void menuCommand_BeforeQueryStatus(object sender, EventArgs e)
    {
      var dte = GetGlobalService(typeof(EnvDTE.DTE)) as EnvDTE.DTE;
      var isActive = dte.ActiveDocument.FullName.EndsWith(".dfy");
      menuCommand.Visible = isActive;
      menuCommand.Enabled = isActive;
    }

    void compileCommand_BeforeQueryStatus(object sender, EventArgs e)
    {
      var dte = GetGlobalService(typeof(EnvDTE.DTE)) as EnvDTE.DTE;
      Microsoft.Dafny.Program program;
      DafnyLanguage.ResolverTagger.Programs.TryGetValue(dte.ActiveDocument.FullName, out program);
      compileCommand.Enabled = (program != null);
    }

    #endregion


    /// <summary>
    /// This function is the callback used to execute a command when the a menu item is clicked.
    /// See the Initialize method to see how the menu item is associated to this function using
    /// the OleMenuCommandService service and the MenuCommand class.
    /// </summary>
    private void CompileCallback(object sender, EventArgs e)
    {
      var dte = GetGlobalService(typeof(EnvDTE.DTE)) as EnvDTE.DTE;
      Microsoft.Dafny.Program program;
      DafnyLanguage.ResolverTagger.Programs.TryGetValue(dte.ActiveDocument.FullName, out program);

      if (program != null)
      {
        IVsStatusbar statusBar = (IVsStatusbar)GetGlobalService(typeof(SVsStatusbar));
        uint cookie = 0;
        statusBar.Progress(ref cookie, 1, "Compiling...", 0, 0);

        DafnyDriver.Compile(program);

        statusBar.Progress(ref cookie, 0, "", 0, 0);
      }
    }
  }
}
