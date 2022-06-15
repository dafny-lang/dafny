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

  [FeatureDescription("Real numbers")]
  RealNumbers,

  [FeatureDescription("Iterators")] 
  Iterators,
  
  [FeatureDescription("Collections with trait element types")] 
  CollectionsOfTraits,
  
  [FeatureDescription("User-defined types with traits as type parameters")] 
  TraitTypeParameters,

  [FeatureDescription("Package names with only underscores")] 
  AllUnderscorePackageNames,
  
  [FeatureDescription("Co-inductive datatypes")] 
  Codatatypes,
  
  [FeatureDescription("Multisets")] 
  Multisets,
  
  [FeatureDescription("Runtime type descriptors")] 
  RuntimeTypeDescriptors,
  
  [FeatureDescription("Multi-dimensional arrays")]
  MultiDimensionalArrays,
  
  [FeatureDescription("Map comprehensions")]
  MapComprehensions,
  
  [FeatureDescription("Traits")]
  Traits,
  
  [FeatureDescription("Let-such-that expressions")]
  LetSuchThatExpressions,
  
  [FeatureDescription("Non-native numeric newtypes")]
  NonNativeNewtypes,
  
  [FeatureDescription("Method synthesis")]
  Synthesis
}

public class UnsupportedFeatureException : Exception {
  
  public const string MessagePrefix =
    "Feature not supported for this compilation target: ";
  
  public readonly IToken Token;
  public readonly Feature Feature;

  public UnsupportedFeatureException(IToken token, Feature feature)
    : this(token, feature, MessagePrefix + FeatureDescriptionAttribute.GetDescription(feature)) {
    
  }
  
  public UnsupportedFeatureException(IToken token, Feature feature, string message) : base(message) {
    Token = token;
    Feature = feature;
  }
}