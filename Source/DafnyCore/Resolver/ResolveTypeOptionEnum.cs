namespace Microsoft.Dafny;

/// <summary>
/// If ResolveType/ResolveTypeLenient encounters a (datatype or class) type "C" with no supplied arguments, then
/// the ResolveTypeOption says what to do.  The last three options take a List as a parameter, which (would have
/// been supplied as an argument if C# had datatypes instead of just enums, but since C# doesn't) is supplied
/// as another parameter (called 'defaultTypeArguments') to ResolveType/ResolveTypeLenient.
/// </summary>
public enum ResolveTypeOptionEnum {
  /// <summary>
  /// never infer type arguments
  /// </summary>
  DontInfer,
  /// <summary>
  /// create a new InferredTypeProxy type for each needed argument
  /// </summary>
  InferTypeProxies,
  /// <summary>
  /// if at most defaultTypeArguments.Count type arguments are needed, use a prefix of defaultTypeArguments
  /// </summary>
  AllowPrefix,
  /// <summary>
  /// same as AllowPrefix, but if more than defaultTypeArguments.Count type arguments are needed, first
  /// extend defaultTypeArguments to a sufficient length
  /// </summary>
  AllowPrefixExtend,
}