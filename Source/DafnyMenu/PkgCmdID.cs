// PkgCmdID.cs
// MUST match PkgCmdID.h
using System;

namespace DafnyLanguage.DafnyMenu
{
  static class PkgCmdIDList
  {
    public const uint cmdidCompile = 0x100;
    public const uint cmdidRunVerifier = 0x101;
    public const uint cmdidStopVerifier = 0x102;
    public const uint cmdidMenu = 0x1021;
    public static uint cmdidToggleSnapshotVerification = 0x103;
    public const uint cmdidToggleBVD = 0x104;
  };
}