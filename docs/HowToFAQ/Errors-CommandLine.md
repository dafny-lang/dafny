## Error: Invalid argument _argument_ to option _option_

```dafny
dafny -functionSyntax:2 null.dfy
```

This is a generic error message about command-line arguments,
indicating that the value given (after the `:` or `=` or as the next command-line argument) is not recognized as a valid value for the given option.

The correct spellings of the valid values should be stated 
in the help document (`dafny -?` or `dafny <command> -h`).
