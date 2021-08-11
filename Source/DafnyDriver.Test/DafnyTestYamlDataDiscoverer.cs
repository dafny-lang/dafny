using System.IO;
using DafnyDriver.Test.XUnitExtensions;
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

    private static DafnyTestSpec SpecForFileName(string fileName) {
      string filePath = fileName.Substring("TestFiles/DafnyTests/Test".Length + 1);
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
    
    public override IParser GetYamlParser(string fileName, Stream stream) {
      string content = GetTestCaseConfigYaml(new StreamReader(stream).ReadToEnd()) ?? DEFAULT_CONFIG;
  
      return new Parser(new StringReader(content));
    }

    public override IDeserializer GetDeserializer(string fileName) {
      var defaultObjectFactory = new DefaultObjectFactory();
      var customObjectFactory = new LambdaObjectFactory(type => 
        type == typeof(DafnyTestSpec) ? SpecForFileName(fileName) : defaultObjectFactory.Create(type));
      
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
  public DafnyTestDataAttribute() : base(false, null, ".dfy") {
  }
}