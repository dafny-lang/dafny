#nullable disable

namespace Microsoft.Dafny;

public enum CoverageLabel {
  None,
  FullyCovered,
  NotCovered,
  PartiallyCovered,
}

public static class CoverageLabelExtension {

  /// <summary>
  /// Combine coverage labels. E.g. FullyCovered + NotCovered = PartiallyCovered
  /// </summary>
  public static CoverageLabel Combine(CoverageLabel one, CoverageLabel two) {
    if (one == CoverageLabel.None) {
      return two;
    }
    if (two == CoverageLabel.None) {
      return one;
    }
    if (one == CoverageLabel.PartiallyCovered || two == CoverageLabel.PartiallyCovered || one != two) {
      return CoverageLabel.PartiallyCovered;
    }
    return one;
  }

  public static string ToString(CoverageLabel label) {
    return label switch {
      CoverageLabel.FullyCovered => "fully covered",
      CoverageLabel.NotCovered => "not covered",
      CoverageLabel.PartiallyCovered => "partially covered",
      _ => ""
    };
  }

}