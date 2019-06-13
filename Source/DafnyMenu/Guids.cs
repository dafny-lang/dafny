// Guids.cs
// MUST match guids.h
using System;

namespace DafnyLanguage.DafnyMenu
{
  static class GuidList
  {
    public const string guidDafnyMenuPkgString = "e1baf989-88a6-4acf-8d97-e0dc243476aa";
    public const string guidDafnyMenuCmdSetString = "393ad46d-e125-41ce-84ee-b4d552d5ba16";
    public const string guidDanfyContextMenuCmdSetString = "5FC4BE4C-AB07-4FD2-A255-6E69E049C113";

    public static readonly Guid guidDafnyMenuCmdSet = new Guid(guidDafnyMenuCmdSetString);
    public static readonly Guid guidDafnyMenuPkgSet = new Guid(guidDafnyMenuPkgString);
    public static readonly Guid guidDanfyContextMenuCmdSet = new Guid(guidDanfyContextMenuCmdSetString);


    public const string guidBvdToolboxPkgString = "8b93ddf6-009c-46b9-a0d2-628405a4e466";
    public const string guidBvdToolboxCmdSetString = "11635790-762b-495f-8c85-9de3a8fe91bd";
    public const string guidToolWindowPersistanceString = "6f1cb50b-18fa-4d03-b480-71be56c50053";

    public static readonly Guid guidBvdToolboxCmdSet = new Guid(guidBvdToolboxCmdSetString);
  };
}
