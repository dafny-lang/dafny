# Process Documentation: Adding New Language Features to Dafny

This documents the general process for adding new language features to Dafny, based on implementing scientific notation and dot shorthand support for real literals (PR #6286).

## Overview of Language Feature Development

Adding a new language feature to Dafny typically involves:
1. **Grammar changes** (parsing new syntax)
2. **AST modifications** (if needed for new constructs)
3. **Semantic analysis** (type checking, resolution)
4. **Code generation** (compilation to target languages)
5. **Testing** (comprehensive coverage)
6. **Documentation** (user-facing and internal)
7. **Release notes** (changelog entry)

## Step-by-Step Process

### 1. Grammar Implementation
**Primary File**: `Source/DafnyCore/Dafny.atg`

**Process**:
- **Locate relevant grammar rules**: Find existing rules that are similar to your feature
- **Extend or add grammar productions**: Use Coco/R syntax
- **Consider precedence and associativity**: Order of alternatives matters
- **Test incrementally**: Small changes, frequent testing

**Common Patterns**:
- **Tokens**: Define new terminal symbols (keywords, operators, literals)
- **Productions**: Define new non-terminal rules for syntax structures
- **Alternatives**: Use `|` to separate different syntax options
- **Optional elements**: Use `[...]` for optional parts
- **Repetition**: Use `{...}` for zero-or-more repetition

**Key Considerations**:
- Maintain backward compatibility
- Follow existing naming conventions
- Consider how the grammar interacts with existing constructs

### 2. AST and Semantic Analysis
**Potential Files**:
- `Source/DafnyCore/AST/` (AST node definitions)
- `Source/DafnyCore/Resolver/` (name resolution, type checking)
- `Source/DafnyCore/Verifier/` (verification condition generation)

**Process**:
- **Check if existing AST nodes suffice**: Sometimes new syntax maps to existing constructs
- **Add new AST nodes if needed**: Inherit from appropriate base classes
- **Update resolution logic**: Handle new constructs in name resolution
- **Update type checking**: Ensure new constructs are properly typed
- **Update verification**: Generate appropriate verification conditions

### 3. Code Generation (if needed)
**Files**: `Source/DafnyCore/Compilers/` (various target language compilers)

**Process**:
- **Determine if compilation changes needed**: Some features are compile-time only
- **Update relevant compilers**: C#, Go, Python, Java, JavaScript, etc.
- **Maintain semantic equivalence**: Ensure compiled code behaves correctly
- **Test compilation**: Verify generated code works in target languages

### 4. Comprehensive Testing
**Location**: `Source/IntegrationTests/TestFiles/LitTests/LitTest/`

**Testing Strategy**:
- **Positive tests**: Valid usage of the new feature
- **Negative tests**: Invalid syntax should be rejected
- **Edge cases**: Boundary conditions, unusual combinations
- **Integration tests**: How feature interacts with existing constructs
- **Compilation tests**: If feature affects code generation

**Test File Naming**:
- `FeatureName.dfy` - main positive tests
- `FeatureNameErrors.dfy` - error/negative tests
- `FeatureNameResolution.dfy` - resolution-specific tests
- `FeatureNameCompilation.dfy` - compilation-specific tests

**Test Commands**:
- `%verify` - full verification pipeline
- `%resolve` - parsing and resolution only
- `%run` - compilation and execution
- `%exits-with N` - expect specific exit code

**Best Practices**:
- Use `var` instead of `ghost var` for simple tests
- Chain assertions when testing equivalences
- Group related test cases in methods
- Include clear comments explaining test purpose

### 5. Documentation Updates
**Files to Update**:
- `docs/DafnyRef/Grammar.md` - formal grammar specification
- `docs/DafnyRef/Types.md` - type system documentation
- `docs/DafnyRef/Expressions.md` - expression documentation
- `docs/DafnyRef/Statements.md` - statement documentation
- Other relevant reference sections

**Documentation Strategy**:
- **Establish consistent vocabulary**: Define terms and use them consistently
- **Provide clear examples**: Show syntax and expected behavior
- **Explain semantics**: What the feature means, not just syntax
- **Maintain formatting consistency**: Match existing line lengths (~70-75 chars)
- **Update all relevant sections**: Don't leave gaps in documentation

**Structure Pattern**:
1. **Introduction**: Brief overview of the feature
2. **Syntax**: Formal grammar or syntax description
3. **Semantics**: What the feature means/does
4. **Examples**: Practical usage examples
5. **Interactions**: How it works with other features

### 6. Release Notes
**File**: `docs/dev/news/<identifier>.<type>`

**Naming Convention**:
- `<PR_number>.<type>` - links to specific PR
- `<description>.<type>` - links to PR that adds the file
- Types: `feat` (features), `fix` (bug fixes), `break` (breaking changes)

**Content Guidelines**:
- **Be concise but complete**: Cover main aspects without being verbose
- **Use practical examples**: Show real value, avoid redundant examples
- **Match documentation vocabulary**: Consistency across all materials
- **Focus on user impact**: What can users now do that they couldn't before?

### 7. Git Workflow
```bash
# Create feature branch
git checkout -b feature_name

# Make changes incrementally
# Test frequently during development

# Add relevant files (be selective)
git add <grammar_files>
git add <documentation_files>
git add <test_files>
git add <release_note>

# Commit with descriptive message
git commit -m "feat: Add [feature description]

- Key capability 1
- Key capability 2
- Key capability 3
- Update grammar/documentation/tests"

# Push to remote
git push origin feature_name
```

## Key Considerations by Feature Type

### New Expressions
- Update expression grammar
- Consider operator precedence
- Add type checking rules
- Update all target compilers
- Test in various contexts (assertions, assignments, etc.)

### New Statements
- Update statement grammar
- Consider control flow implications
- Update verification condition generation
- Test with various statement combinations
- Consider ghost vs. compiled contexts

### New Types
- Update type grammar
- Add type checking and inference rules
- Update subtyping relationships
- Consider default values and initialization
- Update all compilers for type representation

### New Declarations
- Update declaration grammar
- Consider scoping and visibility rules
- Update name resolution
- Consider module system interactions
- Test with various access patterns

## Common Pitfalls to Avoid

### Grammar Issues
- **Ambiguous grammar**: Ensure grammar is unambiguous
- **Precedence problems**: Consider operator precedence carefully
- **Keyword conflicts**: Avoid conflicting with existing keywords
- **Backward compatibility**: Don't break existing valid programs

### Testing Gaps
- **Insufficient error testing**: Test malformed syntax thoroughly
- **Missing edge cases**: Consider boundary conditions
- **Integration gaps**: Test interaction with existing features
- **Platform differences**: Consider target language differences

### Documentation Issues
- **Inconsistent terminology**: Establish vocabulary early and stick to it
- **Missing examples**: Provide practical, realistic examples
- **Incomplete coverage**: Update all relevant documentation sections
- **Formatting inconsistencies**: Match existing documentation style

### Release Process
- **Vague release notes**: Be specific about what users can now do
- **Missing context**: Explain why the feature is useful
- **Poor examples**: Avoid examples that don't show real value

## Testing and Validation

### Before Submitting PR
- [ ] Grammar compiles without errors
- [ ] All new tests pass
- [ ] Existing tests still pass
- [ ] Documentation builds correctly
- [ ] Examples in documentation work
- [ ] Release note is clear and accurate

### Review Checklist
- [ ] Grammar changes are minimal and focused
- [ ] Test coverage is comprehensive
- [ ] Documentation is complete and consistent
- [ ] Release note accurately describes the feature
- [ ] No unrelated files included in commit
- [ ] Commit message is descriptive

## File Organization Reference

### Core Language Files
- `Source/DafnyCore/Dafny.atg` - Grammar specification
- `Source/DafnyCore/AST/` - Abstract syntax tree definitions
- `Source/DafnyCore/Resolver/` - Name resolution and type checking
- `Source/DafnyCore/Verifier/` - Verification condition generation

### Compiler Files
- `Source/DafnyCore/Compilers/` - Target language compilers

### Test Files
- `Source/IntegrationTests/TestFiles/LitTests/LitTest/` - Integration tests
- Various subdirectories for different test categories

### Documentation Files
- `docs/DafnyRef/` - Language reference documentation
- `docs/dev/news/` - Release notes for individual features

This generalized process provides a framework for adding any new language feature to Dafny while maintaining code quality, documentation standards, and user experience.
