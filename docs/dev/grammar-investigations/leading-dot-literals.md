# Leading Dot Literals Investigation

## Summary

This document summarizes an investigation into adding support for leading dot real literals (e.g., `.5` instead of `0.5`) to the Dafny language grammar.

## Background

Many programming languages support leading dot notation for real literals:
- `.5` instead of `0.5`
- `.123` instead of `0.123`
- `.5e2` instead of `0.5e2` (with scientific notation)

This feature was requested to improve code readability and consistency with other languages.

## Investigation Approach

We conducted an exhaustive exploration of 26+ different implementation approaches:

### Token-Level Approaches
1. **Full token-level support** - Add leading dot patterns to `realnumber` token
2. **Restricted patterns** - Only allow 2+ digits, scientific notation only
3. **Context-sensitive tokens** - Use `CONTEXT` keyword for conditional tokenization
4. **Multiple token definitions** - Define overlapping patterns with precedence
5. **Custom scanner states** - Modify generated scanner state machine

### Parser-Level Approaches
6. **Parser-level lookahead** - Use `IF()` conditions in grammar productions
7. **Custom parser productions** - Create `LeadingDotLiteral` production
8. **Dec-level modifications** - Handle leading dots in decimal parsing
9. **Expression context detection** - Parse based on expression start context
10. **Negative lookahead** - Prevent conflicts using grammar restrictions

### Advanced Techniques
11. **Context-aware scanner** - Track parsing context during tokenization
12. **Lexical states** - Switch scanner modes based on context
13. **Semantic actions** - Use code actions to decide tokenization
14. **Post-processing token stream** - Transform tokens after scanning
15. **Custom token types** - Create ambiguous tokens resolved in parser
16. **Manual scanner modification** - Direct modification of generated code
17. **Parser-level token rewriting** - Intercept and modify token stream
18. **Backtracking parser** - Try multiple alternatives with backtracking
19. **Whitespace-sensitive parsing** - Use whitespace context for disambiguation
20. **Precedence-based resolution** - Resolve conflicts through operator precedence

### DotSuffix Modifications
21. **Modify DotSuffix logic** - Extend existing real number handling
22. **Token splitting** - Split real tokens in member access contexts
23. **Pre-processing** - Transform tokens before parsing begins

## Fundamental Conflict Identified

The core issue is an **unavoidable conflict** between:
- **Leading dot literals**: `.5`, `.10`, `.123`
- **Tuple member access**: `tuple.5`, `tuple.10`, `tuple.123`

### Root Cause Analysis

1. **Scanner-level tokenization**: The scanner must decide how to tokenize `.5` without knowing the parsing context
2. **LL(1) grammar limitations**: Cannot use arbitrary lookahead to resolve ambiguity
3. **Greedy tokenization**: Scanner always chooses the longest possible match
4. **Context unavailability**: Member access context isn't available during tokenization

### Specific Conflicts

```dafny
// These would work (leading dot literals)
var a := .5;         // 0.5
var b := .123;       // 0.123
var c := .5e2;       // 50.0

// These would break (tuple member access)
var tuple := (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14);
var d := tuple.5;    // ERROR: .5 parsed as leading dot literal
var e := tuple.10;   // ERROR: .10 parsed as leading dot literal
var f := tuple.123;  // ERROR: .123 parsed as leading dot literal
```

## Attempted Solutions

### Token-Level Solutions
- **Issue**: Any pattern starting with `.` followed by digits conflicts with member access
- **Result**: Either leading dots work and tuple access breaks, or vice versa

### Parser-Level Solutions  
- **Issue**: Conflicts occur during tokenization, before parser context is available
- **Result**: LL(1) lookahead insufficient to resolve ambiguity

### Advanced Techniques
- **Issue**: Coco/R parser generator limitations and architecture constraints
- **Result**: Complex implementations with maintenance burden and uncertain reliability

## Partial Solutions Considered

### Scientific Notation Only
```dafny
// This would work without conflicts:
'.' digit {['_'] digit} ('e'|'E') ['+'|'-'] digit {['_'] digit}

// Supports:
var a := .5e2;       // 50.0 (unambiguous - scientific notation)
var b := .123E-4;    // 0.0000123 (unambiguous - scientific notation)

// Still requires:
var c := 0.5;        // Plain decimals (not .5)

// Preserves:
var d := tuple.5;    // Member access (no conflict)
```

**Benefits**: No conflicts, meaningful use cases covered
**Drawbacks**: Inconsistent support (only scientific notation)

## Decision

After exhaustive investigation, we determined that **full leading dot support cannot be implemented cleanly** without breaking existing functionality or introducing significant complexity.

### Reasons for Rejection

1. **Fundamental grammar conflict** - Cannot be resolved within LL(1) limitations
2. **Breaking changes** - Would break existing tuple member access
3. **Inconsistent behavior** - Partial solutions create confusing edge cases
4. **Maintenance burden** - Complex workarounds difficult to maintain
5. **Architecture constraints** - Coco/R limitations prevent clean solutions

### Alternative Recommendation

Users can continue writing `0.5` instead of `.5` - a small syntactic difference that ensures:
- ✅ **Consistent behavior** across all contexts
- ✅ **No breaking changes** to existing code
- ✅ **Reliable parsing** without edge cases
- ✅ **Maintainable grammar** without complex workarounds

## Lessons Learned

1. **Grammar design is constrained** by parser generator capabilities
2. **LL(1) limitations** can prevent seemingly simple features
3. **Context-sensitive parsing** is difficult in traditional parser generators
4. **Exhaustive exploration** is valuable for understanding fundamental limitations
5. **Sometimes the right decision** is not to implement a feature

## Future Considerations

If Dafny ever migrates to a more powerful parser generator (e.g., ANTLR with backtracking, hand-written recursive descent), leading dot literals could be reconsidered. However, the cost-benefit analysis would need to account for:

- Migration complexity
- Backward compatibility
- Testing burden
- Documentation updates
- User confusion during transition

For now, the current grammar provides reliable, predictable behavior that serves Dafny's verification-focused use cases well.
