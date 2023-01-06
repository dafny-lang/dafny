<!-- DafnyCore/DafnyOptions.cs -->

<!-- TODO: Errors in PrintMode? -->
<!-- TODO: Errors in diagnosticsFormat? -->

## Error: Invalid argument _argument_ to option _option_

```bash <!-- %check-error -->
dafny resolve --function-syntax:2 mod.dfy
```

This is a generic error message about command-line arguments,
indicating that the value given (after the `:` or `=` or as the next command-line argument) is not recognized as a valid value for the given option.

The correct spellings of the valid values should be stated 
in the help document (`dafny -?` or `dafny <command> -h`).

## Error: Invalid argument _argument_ to option --quantifier-syntax

```bash <!-- %check-error -->
dafny resolve --quantifier-syntax:2 null.dfy
```

This is a generic error message about command-line arguments,
indicating that the value given (after the `:` or `=` or as the next command-line argument) is not recognized as a valid value for the given option.

The correct spellings of the valid values should be stated 
in the help document (`dafny -?` or `dafny <command> -h`).


<!-- TODO: Errors in printIncludes? -->
<!-- TODO: Errors in verificationLogger? -->
<!-- TODO: Errors in testContracts? -->

<!-- TODO: Error: Option _name_ unrecognized or unsupported in ':options' attributes. -->

