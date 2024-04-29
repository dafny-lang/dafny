#nullable enable
using System;
using System.Reflection.Metadata;

namespace Microsoft.Dafny;

/// <summary>
/// Dummy implementation of ICustomAttributeTypeProvider, providing just enough
/// functionality to successfully decode a DafnySourceAttribute value.
/// </summary>
internal class StringOnlyCustomAttributeTypeProvider : ICustomAttributeTypeProvider<System.Type> {
  public System.Type GetPrimitiveType(PrimitiveTypeCode typeCode) {
    if (typeCode == PrimitiveTypeCode.String) {
      return typeof(string);
    }
    throw new NotImplementedException();
  }

  public System.Type GetTypeFromDefinition(MetadataReader reader, TypeDefinitionHandle handle, byte rawTypeKind) {
    throw new NotImplementedException();
  }

  public System.Type GetTypeFromReference(MetadataReader reader, TypeReferenceHandle handle, byte rawTypeKind) {
    throw new NotImplementedException();
  }

  public System.Type GetSZArrayType(System.Type elementType) {
    throw new NotImplementedException();
  }

  public System.Type GetSystemType() {
    throw new NotImplementedException();
  }

  public System.Type GetTypeFromSerializedName(string name) {
    throw new NotImplementedException();
  }

  public PrimitiveTypeCode GetUnderlyingEnumType(System.Type type) {
    throw new NotImplementedException();
  }

  public bool IsSystemType(System.Type type) {
    throw new NotImplementedException();
  }
}