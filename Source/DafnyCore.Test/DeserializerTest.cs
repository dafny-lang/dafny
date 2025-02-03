using Microsoft.Dafny;
using Microsoft.Extensions.Logging.Abstractions;
using Serilog.Core;

namespace DafnyCore.Test;

public class DeserializerTest {

  [Fact]
  public async Task Deserialize() {
    var input =
      "0,0,0,0,0,0,0,0,0,0,0,0,\"foo\",],0,null,null,+ClassDecl:0,0,0,0,0,0,0,0,0,0,0,0,\"foo\",null,],+Method:0,0,0,0,0,0,0,0,0,0,0,0,\"foo\",null,true,false,],],],],0,0,0,0,0,0,],null,0,0,0,0,0,0,],null,],0,0,0,0,0,0,],null,0,0,0,0,0,0,null,+AssertStmt:0,0,0,0,0,0,null,+LiteralExpr:0,0,0,0,0,0,+Boolean:true,null],null,false],],false]";
    var options = DafnyOptions.Default;
    var reporter = new BatchErrorReporter(options);
    var output = await ProgramParser.Parse(input, new Uri("file://test.java"), reporter);
    var b = 3;
  }
}