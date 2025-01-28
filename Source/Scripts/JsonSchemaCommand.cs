using System.CommandLine;
using System.Diagnostics;
using System.IO.Compression;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Runtime.Serialization;
using System.Text.Json;
using System.Text.Json.Serialization;
using System.Text.RegularExpressions;
using Microsoft.Dafny;
using Namotion.Reflection;
using NJsonSchema;
using NJsonSchema.Converters;
using NJsonSchema.Generation;
using JsonConstructorAttribute = Newtonsoft.Json.JsonConstructorAttribute;

namespace IntegrationTests;

public class JsonSchemaCommand {

  public static Command GetCommand() {
    var result = new Command("json-schema", "");
    var fileArgument = new Argument<FileInfo>();
    result.AddArgument(fileArgument);
    result.SetHandler(file => Handle(file.Name), fileArgument);
    return result;
  }

  public static async Task Handle(string file) {
    var schema = JsonSchema.FromType<ModuleDefinition>(new SystemTextJsonSchemaGeneratorSettings {
      ReflectionService = new CustomReflectionService()
    });
    var schemaData = schema.ToJson();
    await File.WriteAllTextAsync(file + ".jschema", schemaData);

    var schema2 = JsonSchema.FromType<CProgram>();
    var p = new Caddition(3, new Citeral(1, 3), new Citeral(2, 2));
    
    await File.WriteAllTextAsync(file + ".C.real.json", JsonSerializer.Serialize<Cexpression>(p, new JsonSerializerOptions() {
      
    }));
    await File.WriteAllTextAsync(file + ".C.example.json", schema2.ToSampleJson().ToString());
    await File.WriteAllTextAsync(file + ".C.jschema", schema2.ToJson());
  }

  class CustomReflectionService : SystemTextJsonReflectionService {
    public override void GenerateProperties(JsonSchema schema, ContextualType contextualType,
      SystemTextJsonSchemaGeneratorSettings settings, JsonSchemaGenerator schemaGenerator,
      JsonSchemaResolver schemaResolver) {
      // if (contextualType.Type == typeof(IOrigin)) {
      //   var newContextualType = typeof(SourceOrigin).ToContextualType();
      //   GenerateProperties(schema, newContextualType, settings, schemaGenerator, schemaResolver);
      //   return;
      // }
      if (contextualType.Type.IsInterface) {
        return;
      }

      var constructors = contextualType.Type.GetConstructors(BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic).
          Where(c => c.GetCustomAttribute<CompilerGeneratedAttribute>() == null &&
                     (c.GetParameters().Length == 0 || c.GetParameters()[0].ParameterType != typeof(Cloner))).ToList();
      var jsonConstructor = constructors.Count == 1 ? constructors[0] : constructors.
        FirstOrDefault(c => c.GetCustomAttribute<JsonConstructorAttribute>() != null);
      if (jsonConstructor != null) {
        var propertiesByName = contextualType.Properties.OfType<ContextualAccessorInfo>().
          Concat(contextualType.Fields.Where(f => f.FieldInfo.IsPublic)).
          ToDictionary(p => p.Name.ToLower(), p => p);
        foreach (var parameter in jsonConstructor.GetParameters()) {
          var accessorInfo = propertiesByName[parameter.Name.ToLower()];
          if (accessorInfo.MemberInfo.DeclaringType != contextualType.Type) {
            continue;
          }
          var propertyTypeDescription = GetDescription(accessorInfo.AccessorType, settings.DefaultReferenceTypeNullHandling, settings);
          var propertyName = GetPropertyName(accessorInfo, settings);
          Attribute requiredAttribute = null;
          var hasRequiredAttribute = false;
          var isNullable = false;
          schemaGenerator.AddProperty(schema, accessorInfo, propertyTypeDescription, propertyName, requiredAttribute, hasRequiredAttribute, isNullable, null, schemaResolver);
        }
        return;
      }

      throw new Exception();
      foreach (var accessorInfo in contextualType.Properties.OfType<ContextualAccessorInfo>().Concat(contextualType.Fields))
      {
          if (accessorInfo.MemberInfo.DeclaringType != contextualType.Type ||
              (accessorInfo.MemberInfo is FieldInfo fieldInfo && (fieldInfo.IsPrivate || fieldInfo.IsStatic || !fieldInfo.IsDefined(typeof(DataMemberAttribute)))))
          {
              continue;
          }

          if (accessorInfo.MemberInfo is PropertyInfo propertyInfo &&
              (propertyInfo.GetMethod == null || propertyInfo.GetMethod.IsPrivate == true || propertyInfo.GetMethod.IsStatic == true) &&
              (propertyInfo.SetMethod == null || propertyInfo.SetMethod.IsPrivate == true || propertyInfo.SetMethod.IsStatic == true) &&
              !propertyInfo.IsDefined(typeof(DataMemberAttribute)))
          {
              continue;
          }

          if (accessorInfo.Name == "EqualityContract" &&
              accessorInfo.IsAttributeDefined<CompilerGeneratedAttribute>(true))
          {
              continue;
          }

          if (accessorInfo.MemberInfo is PropertyInfo propInfo &&
              propInfo.GetIndexParameters().Length > 0)
          {
              continue;
          }

          var propertyIgnored = false;
          var jsonIgnoreAttribute = accessorInfo
              .GetAttributes(true)
              .FirstAssignableToTypeNameOrDefault("System.Text.Json.Serialization.JsonIgnoreAttribute", TypeNameStyle.FullName);

          if (jsonIgnoreAttribute != null)
          {
              var condition = jsonIgnoreAttribute.TryGetPropertyValue<object>("Condition");
              if (condition is null || condition.ToString() == "Always")
              {
                  propertyIgnored = true;
              }
          }

          var ignored = propertyIgnored
              || schemaGenerator.IsPropertyIgnoredBySettings(accessorInfo)
              || accessorInfo.GetAttributes(true)
                  .FirstAssignableToTypeNameOrDefault("System.Text.Json.Serialization.JsonExtensionDataAttribute", TypeNameStyle.FullName) != null
              || settings.ExcludedTypeNames.Contains(accessorInfo.AccessorType.Type.FullName);

          if (!ignored)
          {
              var propertyTypeDescription = GetDescription(accessorInfo.AccessorType, settings.DefaultReferenceTypeNullHandling, settings);
              var propertyName = GetPropertyName(accessorInfo, settings);

              var propertyAlreadyExists = schema.Properties.ContainsKey(propertyName);
              if (propertyAlreadyExists)
              {
                  if (settings.GetActualFlattenInheritanceHierarchy(contextualType.Type))
                  {
                      schema.Properties.Remove(propertyName);
                  }
                  else
                  {
                      throw new InvalidOperationException($"The JSON property '{propertyName}' is defined multiple times on type '{contextualType.Type.FullName}'.");
                  }
              }

              var requiredAttribute = accessorInfo
                  .GetAttributes(true)
                  .FirstAssignableToTypeNameOrDefault("System.ComponentModel.DataAnnotations.RequiredAttribute");

              var isDataContractMemberRequired = schemaGenerator.GetDataMemberAttribute(accessorInfo, contextualType.Type)?.IsRequired == true;

              var hasRequiredAttribute = requiredAttribute != null;
              if (hasRequiredAttribute || isDataContractMemberRequired)
              {
                  schema.RequiredProperties.Add(propertyName);
              }

              var isNullable = propertyTypeDescription.IsNullable && hasRequiredAttribute == false;

              // TODO: Add default value
              schemaGenerator.AddProperty(schema, accessorInfo, propertyTypeDescription, propertyName, requiredAttribute, hasRequiredAttribute, isNullable, null, schemaResolver);
          }
      }
    }
  }
}

[Newtonsoft.Json.JsonConverter(typeof(JsonInheritanceConverter<Bexpression>), "discriminator")]
[KnownType(typeof(Baddition))]
[KnownType(typeof(Biteral))]
abstract class Bexpression {
  public int Position { get; set; }
}

class Baddition : Bexpression {
  public Bexpression Left { get; }
  public Bexpression Right { get; }
}

class Biteral : Bexpression {
  public int Value { get; }
}

class CProgram {
  public Cexpression Root { get; }
}

[JsonDerivedType(typeof(Caddition), typeDiscriminator: "addition")]
[JsonDerivedType(typeof(Citeral), typeDiscriminator: "literal")]
abstract class Cexpression {
  public int Position { get; set; }

  protected Cexpression(int position) {
    Position = position;
  }
}

class Caddition : Cexpression {
  public Cexpression Left { get; }
  public Cexpression Right { get; }

  public Caddition(int position, Cexpression left, Cexpression right) : base(position) {
    Left = left;
    Right = right;
  }
}

class Citeral : Cexpression {
  public int Value { get; }

  public Citeral(int position, int value) : base(position) {
    Value = value;
  }
}

class Dexpr {
  int position;
}

class Dadd : Dexpr {
  Dexpr left;
  Dexpr right;
}