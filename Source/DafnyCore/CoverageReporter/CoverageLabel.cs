namespace DafnyCore.CoverageReporter;

public enum CoverageLabel {
  FullyCovered,
  NotCovered,
  PartiallyCovered
}

public static class CoverageLabelExtension {

  /// <summary>
  /// Return coverage label for a program location that is covered by several overlapping coverage spans
  /// </summary>
  public static CoverageLabel Combine(CoverageLabel one, CoverageLabel two) {
    if (one == CoverageLabel.PartiallyCovered || two == CoverageLabel.PartiallyCovered || one != two) {
      return CoverageLabel.PartiallyCovered;
    }
    return one;
  }

  public static string OpenHtmlTag(CoverageLabel label) {
    switch (label) {
      case CoverageLabel.FullyCovered:
        return "<span class=\"fc\">";
      case CoverageLabel.NotCovered:
        return "<span class=\"nc\">";
      case CoverageLabel.PartiallyCovered:
        return "<span class=\"pc\">";
    }
    return "";
  }

  public static string CloseHtmlTag(CoverageLabel label) {
    return "</span>";
  }

}