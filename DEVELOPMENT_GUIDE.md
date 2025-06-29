# Dafny Development Guide: Building Language Features

This guide documents best practices for developing language features in the Dafny repository, covering grammar changes, verification enhancements, and tooling improvements.

## Repository Structure

### Core Components
- **`Source/DafnyCore/Dafny.atg`** - Main grammar file (Coco/R format)
- **`Source/DafnyCore/AST/`** - Abstract syntax tree classes
- **`Source/DafnyCore/Resolver/`** - Type checking and name resolution
- **`Source/DafnyCore/Verifier/`** - Verification condition generation
- **`Source/DafnyCore/Compilers/`** - Code generation backends
- **`Source/DafnyDriver/`** - Command-line interface

### Build System
- **Primary**: .NET build system (`dotnet build`, `dotnet run`)
- **Grammar**: Coco/R parser generator (automatically invoked)
- **Testing**: Integration tests, unit tests, and lit tests
- **Documentation**: Markdown files in `docs/`

## Development Workflow

### 1. Initial Setup
```bash
git clone https://github.com/dafny-lang/dafny.git
cd dafny
git checkout -b feature-name
dotnet build Source/DafnyCore/DafnyCore.csproj
```

### 2. Feature Categories

#### **Grammar and Syntax Features**
For adding new language constructs or syntax:
- **Primary files**: `Dafny.atg` (grammar rules)
- **Secondary files**: AST classes, printer, resolver
- **Examples**: New operators, literal formats, statement types

#### **Verification Features**
For enhancing proof capabilities or verification behavior:
- **Primary files**: AST classes, Boogie translation, resolver
- **Secondary files**: Verification condition generation
- **Examples**: New proof constructs, assertion types, specification clauses

#### **Analysis and Tooling**
For developer productivity and code analysis:
- **Primary files**: Analysis classes, command-line options
- **Secondary files**: Result processing, output formatting
- **Examples**: Linting, suggestions, proof debugging

## Grammar Development

### Token Definitions (Lexer)
Located in the `TOKENS` section of `Dafny.atg`:
```
// Define new tokens
newtoken = pattern {pattern} [optional_part].
```

**Key principles:**
- Tokens are matched greedily by the lexer
- More specific patterns should come first
- Use `{...}` for zero-or-more, `[...]` for optional
- Be careful not to break existing token patterns

### Production Rules (Parser)
Located in the main grammar section:
```
ProductionName<out Type result>
= (. // Initialization code .)
  ( alternative1 (. // Semantic action .)
  | alternative2 (. // Semantic action .)
  )
  .
```

**Key principles:**
- Productions define parsing structure
- Semantic actions in `(. ... .)` execute C# code
- Use lookahead `IF(condition)` for disambiguation
- Parameters pass data between rules

### Common Parsing Patterns
- **Lookahead**: `IF(la.kind == _token && scanner.Peek().kind == _other)`
- **Token capture**: `(. var tokenVar = t; .)` before consuming next token
- **Error handling**: `SemErr(ErrorId.error_name, token, "message")`

## AST Development

### Adding New AST Nodes
```csharp
public class NewStatement : Statement {
  public readonly Expression Condition;
  public readonly BlockStmt Body;
  
  public NewStatement(IToken tok, Expression condition, BlockStmt body) 
    : base(tok, tok) {
    Condition = condition;
    Body = body;
  }
  
  public override IEnumerable<INode> Children => 
    new[] { Condition }.Concat(Body?.Children ?? Enumerable.Empty<INode>());
}
```

### Essential AST Patterns
- **Immutable design**: AST nodes should be immutable after construction
- **Visitor pattern**: Implement `Children` property for traversal
- **Cloning support**: Add cloner constructor for transformations
- **Source tracking**: Maintain token information for error reporting

### Cloning Support
```csharp
public NewStatement(Cloner cloner, NewStatement original) : base(cloner, original) {
  Condition = cloner.CloneExpr(original.Condition);
  Body = cloner.CloneBlockStmt(original.Body);
}
```

## Resolution and Type Checking

### Resolver Integration
The resolver performs name resolution, type checking, and semantic analysis:
```csharp
public override void Resolve(ModuleResolver resolver, ResolutionContext context) {
  // Resolve sub-expressions and statements
  resolver.ResolveExpression(Condition, context);
  resolver.ResolveStatement(Body, context);
  
  // Perform semantic checks
  if (!Condition.Type.IsBoolType) {
    resolver.reporter.Error(MessageSource.Resolver, Condition.tok, 
      "condition must be boolean");
  }
}
```

### Type System Integration
- **Type inference**: Let the resolver infer types when possible
- **Type constraints**: Add explicit checks for type requirements
- **Error reporting**: Use descriptive error messages with source locations

## Verification Integration

### Boogie Translation
For verification features, update the Boogie translator:
```csharp
void TrStatement(Statement stmt, BoogieStmtListBuilder builder, 
                 List<Variable> locals, ExpressionTranslator etran) {
  if (stmt is NewStatement newStmt) {
    // Translate to Boogie constructs
    var condition = etran.TrExpr(newStmt.Condition);
    // Generate verification conditions
  }
}
```

### Verification Patterns
- **Preconditions**: Generate `requires` clauses
- **Postconditions**: Generate `ensures` clauses  
- **Loop invariants**: Handle iterative constructs
- **Assertions**: Generate verification conditions

## Testing Strategy

### Test File Organization
```
Source/IntegrationTests/TestFiles/LitTests/LitTest/
├── dafny0/           # Basic language features
├── dafny1/           # Advanced features
├── dafny2/           # Complex examples
└── logger/           # Analysis and tooling tests
```

### Test Types

#### **Positive Tests**
```dafny
// RUN: %testDafnyForEachResolver --expect-exit-code=0 "%s"
// RUN: %diff "%s.expect" "%t"

method TestNewFeature() {
  // Test that new syntax works correctly
  assert new_syntax_example;
}
```

#### **Negative Tests**
```dafny
// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method TestErrors() {
  var invalid := bad_syntax;  // Error: expected message
}
```

#### **Analysis Tests**
```dafny
// RUN: %baredafny verify --analysis-flag --show-hints "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Expected output in .expect file:
// Info: Analysis suggestion or warning
```

### Testing Best Practices
1. **Minimal examples**: Create focused tests for specific features
2. **Edge cases**: Test boundary conditions and error cases
3. **Integration**: Verify interaction with existing features
4. **Regression**: Ensure existing functionality still works

## Build and Development Cycle

### Quick Iteration
```bash
# Build core components
dotnet build Source/DafnyCore/DafnyCore.csproj

# Test specific file
dotnet run --project Source/DafnyDriver/DafnyDriver.csproj -- verify test.dfy

# Run specific test suite
dotnet test Source/DafnyCore.Test/
```

### Full Validation
```bash
# Complete build
dotnet build

# Run integration tests
cd Source/IntegrationTests
lit TestFiles/LitTests/LitTest/dafny0/YourTest.dfy
```

## Common Development Patterns

### Parser Conflict Resolution
**Problem**: `LL1 warning: token is start of several alternatives`
**Solution**: Use lookahead or reorder alternatives
```
| IF(la.kind == _token && scanner.Peek().kind == _other) Production1
| Production2
```

### AST Extension Pattern
When adding fields to existing AST nodes:
1. **Constructor**: Add parameter with default value
2. **Cloner**: Update cloner constructor
3. **Children**: Include in traversal if needed
4. **Printer**: Update syntax printing
5. **Resolver**: Handle in resolution phase

### Error Handling Pattern
```csharp
// In semantic actions
SemErr(ErrorId.p_error_name, token, "descriptive message");

// In resolver
reporter.Error(MessageSource.Resolver, token, "error description");
```

## Documentation Requirements

### Grammar Documentation
Update `docs/DafnyRef/Grammar.md`:
```markdown
A `tokenname` token represents description with examples.
Examples: `example1`, `example2`.
```

### Language Reference
Update relevant sections in `docs/DafnyRef/`:
```markdown
**Feature Name** description with examples.
For example, `syntax_example` produces `expected_result`.
```

### News Entries
Add `docs/dev/news/<PR#>.feat`:
```
Brief description of the new feature for release notes.
```

## Quality Assurance

### Pre-Commit Checklist
- [ ] Grammar changes are minimal and focused
- [ ] All AST changes include cloner support
- [ ] Comprehensive test coverage (positive and negative)
- [ ] Documentation updated consistently
- [ ] No regressions in existing functionality
- [ ] Clear error messages for invalid usage

### CI Validation and Debugging

#### Monitoring CI Progress
```bash
# Monitor CI progress
gh run list --branch feature-branch --limit 5
gh run view <run-id>
gh run view --job=<job-id>

# Get detailed failure logs when standard output doesn't show details
gh api repos/dafny-lang/dafny/actions/jobs/<job-id>/logs
```

#### Common CI Failure Patterns

**Test Expectation Mismatches** (Most Common):
- **Symptom**: Tests fail with diff output showing format differences
- **Example**: Expected `Source/.../file.dfy(8,15): Error` vs Actual `file.dfy(8,15): Error`
- **Root Cause**: Error message format changes (path format, line formatting)
- **Solution**: Update `.expect` files to match actual output

**Integration vs Unit Test Failures**:
- **Unit test failures**: Usually indicate core functionality issues
- **Integration test failures**: Often format/expectation issues, but **all must be fixed**
- **Any integration failures**: Require investigation and resolution

#### Debugging Failed Tests

**Quick Diagnosis**:
```bash
# Get specific error details
gh api repos/dafny-lang/dafny/actions/jobs/<job-id>/logs | grep -A 10 -B 5 "Error:"

# Look for diff patterns in test failures
gh api repos/dafny-lang/dafny/actions/jobs/<job-id>/logs | grep -A 20 "Diff"
```

**Test Expectation Updates**:
```bash
# Common location pattern
Source/IntegrationTests/TestFiles/LitTests/LitTest/*/TestName.dfy.expect

# Update workflow
1. Identify failing test from CI logs
2. Compare expected vs actual output
3. Update .expect file to match actual (usually correct) output
4. Commit and push: git commit -m "Fix test expectation format for TestName"
```

#### CI Workflow Understanding
- **Build and Test**: Main workflow with 5 parallel integration test jobs
- **Standard Libraries**: Separate long-running workflow (can take 30+ minutes)
- **Documentation**: Quick validation of docs and reference manual
- **Runtimes**: Tests for different target language runtimes

#### Healthy CI Indicators
- ✅ Core build succeeds (singletons job)
- ✅ Unit tests pass on all platforms (Windows, macOS, Linux)
- ✅ **All integration test jobs pass** - any failures need to be addressed
- ✅ Documentation builds successfully

**Important**: Integration test failures are **not normal** and must all be fixed. Even 1-2 failures indicate issues that need resolution.

### Code Review Preparation
```bash
# Review complete changes
git diff master..feature-branch

# Ensure clean commit history
git log --oneline master..feature-branch
```

## Best Practices

### Language Design
1. **Consistency**: Follow existing Dafny syntax patterns
2. **Simplicity**: Prefer simple, clear syntax over complex constructs
3. **Orthogonality**: Ensure features compose well together
4. **Backward compatibility**: Don't break existing code

### Implementation Quality
1. **Incremental development**: Build features step by step
2. **Test-driven**: Write tests before implementation
3. **Error handling**: Provide helpful error messages
4. **Performance**: Consider impact on compilation and verification time

### Maintenance
1. **Documentation**: Keep docs synchronized with implementation
2. **Testing**: Maintain comprehensive test coverage
3. **Refactoring**: Clean up code as features evolve
4. **Compatibility**: Consider impact on existing users

## Quick Reference

### Essential Commands
```bash
# Development cycle
dotnet build Source/DafnyCore/DafnyCore.csproj
dotnet run --project Source/DafnyDriver/DafnyDriver.csproj -- verify test.dfy

# Testing
dotnet test
lit TestFiles/LitTests/LitTest/dafny0/

# Review
git diff master..branch
gh pr create
```

### Key File Locations
- **Grammar**: `Source/DafnyCore/Dafny.atg`
- **AST**: `Source/DafnyCore/AST/`
- **Tests**: `Source/IntegrationTests/TestFiles/LitTests/LitTest/`
- **Docs**: `docs/DafnyRef/`
- **News**: `docs/dev/news/`

### Development Workflow
1. **Plan**: Understand the feature requirements and design
2. **Implement**: Make minimal, focused changes
3. **Test**: Add comprehensive test coverage
4. **Document**: Update all relevant documentation
5. **Review**: Use `git diff` to review complete changes
6. **Validate**: Ensure CI passes completely

This guide provides the foundation for professional Dafny language development, emphasizing quality, maintainability, and user experience.
