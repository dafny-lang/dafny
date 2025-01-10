# 15. Plugins to Dafny {#sec-plugins}

Dafny has a plugin architecture that permits users to build tools for the Dafny language without having to replicate 
parsing and name/type resolution of Dafny programs. Such a tool might just do some analysis on the Dafny program,
without concern for verifying or compiling the program. Or it might modify the program (actually, modify the program's AST) 
and then continue on with verification and compilation with the core Dafny tool. A user plugin might also be used
in the Language Server and thereby be available in the VSCode (or other) IDE.

_**This is an experimental aspect of Dafny.**
The plugin API directly exposes the Dafny AST, which is constantly evolving.
Hence, always recompile your plugin against the binary of Dafny that will be importing your plugin._

Plugins are libraries linked to a `Dafny.dll` of the same version as the Language Server.
A plugin typically defines:

* Zero or one class extending `Microsoft.Dafny.Plugins.PluginConfiguration`, which receives plugins arguments in its method `ParseArguments`, and
  1. Can return a list of `Microsoft.Dafny.Plugins.Rewriter`s when its method `GetRewriters()` is called by Dafny,
  2. Can return a list of `Microsoft.Dafny.Plugins.Compiler`s when its method `GetCompilers()` is called by Dafny,
  3. If the configuration extends the subclass `Microsoft.Dafny.LanguageServer.Plugins.PluginConfiguration`:
      1. Can return a list of `Microsoft.Dafny.LanguageServer.Plugins.DafnyCodeActionProvider`s when its method `GetDafnyCodeActionProviders()` is called by the Dafny Language Server.
      2. Can return a modified version of `OmniSharp.Extensions.LanguageServer.Server.LanguageServerOptions` when its method `WithPluginHandlers()` is called by the Dafny Language Server.

* Zero or more classes extending `Microsoft.Dafny.Plugins.Rewriter`.
  If a configuration class is provided, it is responsible for instantiating them and returning them in `GetRewriters()`.
  If no configuration class is provided, an automatic configuration will load every defined `Rewriter` automatically.
* Zero or more classes extending `Microsoft.Dafny.Plugins.Compiler`.
  If a configuration class is provided, it is responsible for instantiating them and returning them in `GetCompilers()`.
  If no configuration class is provided, an automatic configuration will load every defined `Compiler` automatically.
* Zero or more classes extending `Microsoft.Dafny.LanguageServer.Plugins.DafnyCodeActionProvider`.
  Only a configuration class of type `Microsoft.Dafny.LanguageServer.Plugins.PluginConfiguration` can be responsible for instantiating them and returning them in `GetDafnyCodeActionProviders()`.

The most important methods of the class `Rewriter` that plugins override are

* (experimental) `PreResolve(ModuleDefinition)`: Here you can optionally modify the AST before it is resolved.
* `PostResolve(ModuleDefinition)`: This method is repeatedly called with every resolved and type-checked module, before verification.
  Plugins override this method typically to report additional diagnostics.
* `PostResolve(Program)`: This method is called once after all `PostResolve(ModuleDefinition)` have been called.

Plugins are typically used to report additional diagnostics such as unsupported constructs for specific compilers (through the methods `Èrror(...)` and `Warning(...)` of the field `Reporter` of the class `Rewriter`)

Note that all plugin errors should use the original program's expressions' token and NOT `Token.NoToken`, else no error will be displayed in the IDE.

## 15.1. Language Server plugin tutorial

In this section, we will create a plugin that enhances the functionality of the Language Server.
We will start by showing the steps needed to create a plugin, followed by an example implementation that demonstrates how to provide more code actions and add custom request handlers.

### 15.1.1. Create plugin project

Assuming the Dafny source code is installed in the folder `dafny/`
start by creating an empty folder next to it, e.g. `PluginTutorial/`

```bash
mkdir PluginTutorial
cd PluginTutorial
```

Then, create a dotnet class project

```bash
dotnet new classlib
```

It will create a file `Class1.cs` that you can rename

```bash
mv Class1.cs MyPlugin.cs
```

Open the newly created file `PluginTutorial.csproj`, and add the following after `</PropertyGroup>`:

```xml
  <ItemGroup>
    <ProjectReference Include="../dafny/source/DafnyLanguageServer/DafnyLanguageServer.csproj" />
  </ItemGroup>
```
### 15.1.2. Implement plugin

#### 15.1.2.1. Code actions plugin

This code action plugin will add a code action that allows you to place a dummy comment in front of the first method name, only if the selection is on the line of the method.

Open the file `MyPlugin.cs`, remove everything, and write the imports and a namespace:

```csharp
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.Plugins;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using System.Linq;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace MyPlugin;
```

After that, add a `PluginConfiguration` that will expose all the quickfixers of your plugin.
This class will be discovered and instantiated automatically by Dafny.

```csharp
public class TestConfiguration : PluginConfiguration {
  public override DafnyCodeActionProvider[] GetDafnyCodeActionProviders() {
    return new DafnyCodeActionProvider[] { new AddCommentDafnyCodeActionProvider() };
  }
}
```

Note that you could also override the methods `GetRewriters()` and `GetCompilers()` for other purposes, but this is out of scope for this tutorial.

Then, we need to create the quickFixer `AddCommentDafnyCodeActionProvider` itself:

```csharp
public class AddCommentDafnyCodeActionProvider : DafnyCodeActionProvider {
  public override IEnumerable<DafnyCodeAction> GetDafnyCodeActions(IDafnyCodeActionInput input, Range selection) {
    return new DafnyCodeAction[] { };
  }
}
```

For now, this quick fixer returns nothing. `input` is the program state, and `selection` is where the caret is.
We replace the return statement with a conditional that tests whether the selection is on the first line:

```csharp
    var firstTokenRange = input.Program?.GetFirstTopLevelToken()?.GetLspRange();
    if(firstTokenRange != null && firstTokenRange.Start.Line == selection.Start.Line) {
      return new DafnyCodeAction[] {
        // TODO
      };
    } else {
      return new DafnyCodeAction[] { };
    }
```

Every quick fix consists of a title (provided immediately), and zero or more `DafnyCodeActionEdit` (computed lazily).
A `DafnyCodeActionEdit` has a `Range` to remove and some `string` to insert instead. All `DafnyCodeActionEdit`s
of the same `DafnyCodeAction` are applied at the same time if selected.

To create a `DafnyCodeAction`, we can either use the easy-to-use `InstantDafnyCodeAction`, which accepts a title and an array of edits:

```csharp
  return new DafnyCodeAction[] {
    new InstantDafnyCodeAction("Insert comment", new DafnyCodeActionEdit[] {
      new DafnyCodeActionEdit(firstTokenRange.GetStartRange(), "/*First comment*/")
    })
  };
```

or we can implement our custom inherited class of `DafnyCodeAction`:

```csharp
public class CustomDafnyCodeAction: DafnyCodeAction {
  public Range whereToInsert;
  
  public CustomDafnyCodeAction(Range whereToInsert): base("Insert comment") {
    this.whereToInsert = whereToInsert;
  }
  public override DafnyCodeActionEdit[] GetEdits() {
    return new DafnyCodeActionEdit[] {
      new DafnyCodeActionEdit(whereToInsert.GetStartRange(), "/*A comment*/")
    };
  }
}
```

In that case, we could return:

```csharp
  return new DafnyCodeAction[] {
    new CustomDafnyCodeAction(firstTokenRange)
  };
```

#### 15.1.2.2. Request handler plugin

This request handler plugin enhances the Language Server to support a request with a `TextDocumentIdentifier` as parameter, which will return a `bool` value denoting whether the provided `DocumentUri` has any `LoopStmt`'s in it.

Open the file `MyPlugin.cs`, remove everything, and write the imports and a namespace:

```csharp
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Server;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Microsoft.Dafny.LanguageServer.Plugins;
using Microsoft.Dafny.LanguageServer.Workspace;
using MediatR;
using Microsoft.Dafny;

namespace MyPlugin;
```

After that, add a `PluginConfiguration` that will add all the request handlers of your plugin.
This class will be discovered and instantiated automatically by Dafny.

```csharp
public class TestConfiguration : PluginConfiguration {
  public override LanguageServerOptions WithPluginHandlers(LanguageServerOptions options) {
    return options.WithHandler<DummyHandler>();
  }
}
```

Then, we need to create the request handler `DummyHandler` itself:

```csharp
[Parallel]
[Method("dafny/request/dummy", Direction.ClientToServer)]
public record DummyParams : TextDocumentIdentifier, IRequest<bool>;

public class DummyHandler : IJsonRpcRequestHandler<DummyParams, bool> {
  private readonly IProjectDatabase projects;
  public DummyHandler(IProjectDatabase projects) {
    this.projects = projects;
  }
  public async Task<bool> Handle(DummyParams request, CancellationToken cancellationToken) {
    var state = await projects.GetParsedDocumentNormalizeUri(request);
    if (state == null) {
      return false;
    }
    return state.Program.Descendants().OfType<LoopStmt>().Any();
  }
}
```

For more advanced example implementations of request handlers, look at `dafny/Source/DafnyLanguageServer/Handlers/*`.

### 15.1.3. Building plugin

That's it! Now, build your library while inside your folder:

```bash
> dotnet build
```

This will create the file `PluginTutorial/bin/Debug/net8.0/PluginTutorial.dll`.
Now, open VSCode, open Dafny settings, and enter the absolute path to this DLL in the plugins section.
Restart VSCode, and it should work!
