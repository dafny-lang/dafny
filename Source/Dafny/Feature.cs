using System;

namespace Microsoft.Dafny;


public class FeatureDescriptionAttribute : Attribute {
  public readonly string Decription;

  public FeatureDescriptionAttribute(string decription) {
    Decription = decription;
  }
}

public enum Feature {
  [FeatureDescription("iterators")]
  Iterators
}

public class FeatureNotSupportedException : Exception {
  public readonly Feature Feature;

  public FeatureNotSupportedException(Feature feature) {
    Feature = feature;
  }
}