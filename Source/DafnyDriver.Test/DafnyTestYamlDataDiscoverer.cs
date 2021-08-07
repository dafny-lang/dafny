using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using DafnyDriver.Test.XUnitExtensions;
using Microsoft.Extensions.FileProviders;
using Xunit.Sdk;
using XUnitExtensions;
using YamlDotNet.Core;
using YamlDotNet.Serialization;
using YamlDotNet.Serialization.NamingConventions;
using YamlDotNet.Serialization.ObjectFactories;

namespace DafnyDriver.Test {
  public class DafnyTestYamlDataDiscoverer : YamlDataDiscoverer {

    private const string DEFAULT_CONFIG = 
@"!dafnyTestSpec
dafnyArguments: {}
";

    private static readonly IFileProvider ManifestFileProvider = new ManifestEmbeddedFileProvider(
      Assembly.GetExecutingAssembly());
    private static readonly Dictionary<string, string> PathsForResourceNames = GetPathsForResourceNames(
      "DafnyDriver.Test", ManifestFileProvider, "DafnyTests");
    
    private static Dictionary<string, string> GetPathsForResourceNames(string assemblyName, IFileProvider fileProvider, string path = null) {
      return fileProvider.GetDirectoryContents(path).SelectMany(file => {
        var childName = path == null ? file.Name : path + "/" + file.Name;
        if (file.IsDirectory) {
          return GetPathsForResourceNames(assemblyName, fileProvider, childName);
        } else {
          var result = new Dictionary<string, string>();
          result[ResourceNameForFilePath(assemblyName, childName)] = childName;
          return result;
        }
      }).ToDictionary(pair => pair.Key, pair => pair.Value);
    }

    private static string ResourceNameForFilePath(string assemblyName, string filePath) {
      return assemblyName + "." + filePath.Replace("/", ".").Replace("+", "_");
    }
    
    private static DafnyTestSpec SpecForResourceName(string manifestResourceName) {
      string filePath = PathsForResourceNames[manifestResourceName].Substring("DafnyTests/Test".Length + 1);
      return new DafnyTestSpec(filePath);
    }
    
    public static string GetTestCaseConfigYaml(string fullText) {
      var commentStart = fullText.IndexOf("/*");
      if (commentStart >= 0) {
        var commentEnd = fullText.IndexOf("*/", commentStart + 2);
        if (commentEnd >= 0) {
          var commentContent = fullText.Substring(commentStart + 2, commentEnd - commentStart - 2).Trim();
          if (commentContent.StartsWith("---")) {
            return commentContent;
          }
        }
      }

      return null;
    }
    
    public override IParser GetYamlParser(string manifestResourceName, Stream stream) {
      if (!manifestResourceName.EndsWith(".dfy")) {
        return null;
      }
      
      string content = GetTestCaseConfigYaml(new StreamReader(stream).ReadToEnd()) ?? DEFAULT_CONFIG;
  
      return new Parser(new StringReader(content));
    }

    public override IDeserializer GetDeserializer(string manifestResourceName) {
      var defaultObjectFactory = new DefaultObjectFactory();
      var customObjectFactory = new LambdaObjectFactory(type => 
        type == typeof(DafnyTestSpec) ? SpecForResourceName(manifestResourceName) : defaultObjectFactory.Create(type));
      
      return new DeserializerBuilder()
        .WithNamingConvention(CamelCaseNamingConvention.Instance)
        .WithTagMapping("!dafnyTestSpec", typeof(DafnyTestSpec))
        .WithTagMapping("!foreach", typeof(ForEachArgumentList))
        .WithObjectFactory(customObjectFactory)
        .Build();
    }
  }
}

[DataDiscoverer("DafnyDriver.Test.DafnyTestYamlDataDiscoverer", "DafnyDriver.Test")]
public class DafnyTestDataAttribute : YamlDataAttribute {
  public DafnyTestDataAttribute(bool withParameterNames) : base(withParameterNames) {
  }
}