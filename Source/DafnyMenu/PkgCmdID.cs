// PkgCmdID.cs
// MUST match PkgCmdID.h
using System;

namespace DafnyLanguage.DafnyMenu
{
  static class PkgCmdIDList
  {
    public const uint cmdidCompile = 0x10;
    public const uint cmdidRunResolver = 0x11;
    public const uint cmdidStopResolver = 0x12;
    public const uint cmdidRunVerifier = 0x101;
    public const uint cmdidStopVerifier = 0x102;
    public const uint cmdidMenu = 0x1021;
    public static uint cmdidToggleSnapshotVerification = 0x103;
    public const uint cmdidToggleBVD = 0x104;
    public static uint cmdidToggleMoreAdvancedSnapshotVerification = 0x105;
    public static uint cmdidToggleAutomaticInduction = 0x106;
    public static uint cmdidDiagnoseTimeouts = 0x107;
  };
}
