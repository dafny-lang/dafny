// Guids.cs
// MUST match guids.h
using System;

namespace DafnyLanguage.DafnyMenu
{
  static class GuidList
  {
    public const string guidDafnyMenuPkgString = "e1baf989-88a6-4acf-8d97-e0dc243476aa";
    public const string guidDafnyMenuCmdSetString = "393ad46d-e125-41ce-84ee-b4d552d5ba16";

    public static readonly Guid guidDafnyMenuCmdSet = new Guid(guidDafnyMenuCmdSetString);
    public static readonly Guid guidDafnyMenuPkgSet = new Guid(guidDafnyMenuPkgString);
  };
}