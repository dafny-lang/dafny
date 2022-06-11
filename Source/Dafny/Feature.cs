using System;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny; 

public class FeatureDescriptionAttribute : Attribute {
  public readonly string Description;

  public FeatureDescriptionAttribute(string description) {
    Description = description;
  }

  public static string GetDescription(Feature feature) {
    var memberInfo = typeof(Feature).GetMember(feature.ToString()).First();
    var attribute = (FeatureDescriptionAttribute)GetCustomAttribute(memberInfo, typeof(FeatureDescriptionAttribute));
    return attribute!.Description;
  }
  
  public static Feature ForDescription(string description) {
    var memberInfo = typeof(Feature).GetMembers().First(memberInfo => {
      var attribute = (FeatureDescriptionAttribute)GetCustomAttribute(memberInfo, typeof(FeatureDescriptionAttribute));
      return attribute != null && attribute.Description == description;
    });
    return (Feature)Enum.Parse(typeof(Feature), memberInfo.Name);
  }
}

public enum Feature {
  [FeatureDescription("Unbounded integers")]
  UnboundedIntegers,

  [FeatureDescription("Iterators")] Iterators,
}

public class FeatureNotSupportedException : Exception {
  
  public const string MessagePrefix =
    "Feature not supported for this compilation target: ";
  
  public readonly IToken Token;
  public readonly Feature Feature;

  public FeatureNotSupportedException(IToken token, Feature feature)
    : this(token, feature, MessagePrefix + FeatureDescriptionAttribute.GetDescription(feature)) {
    
  }
  
  public FeatureNotSupportedException(IToken token, Feature feature, string message) : base(message) {
    Token = token;
    Feature = feature;
  }
}