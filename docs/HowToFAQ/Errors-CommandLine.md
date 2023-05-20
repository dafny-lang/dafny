
<!-- DafnyDriver/DafnyDriver.cs -->

## **Error: No compiler found for target _target_; expecting one of _known_** {#cli_unknown_compiler}

<!-- %check-cli -->
```bash
dafny build -t:zzz
```

The `-t` or `--target` options specifies which backend compiler to use for 
those dafny commands that compile dafny to other programming languages. 
This error message says that the named language is not supported.

## **Error: No input files were specified in command-line _command_** {#cli_no_files}

<!-- %check-cli -->
```bash
dafny resolve
```

Any valid dafny invocation requires at least one .dfy file. 
The only exceptions are the special commands like `--help` and `--version`.

## **Error: file _name_ not found** {#cli_file_not_found}

<!-- %check-cli -->
```bash
dafny resolve zzz.dfy
```

This error message simply states that the named file could not be found
by the dafny tool. Note that files on the command-line are named
relative to the current working directory of the shell in which the
command is invoked or are absolute file paths.

## **Error: Command-line argument '_arg_' is neither a recognized option nor a filename with a supported extension (_ext_).** {#cli_bad_option}

<!-- %check-cli -->
```bash
dafny resolve --zzz
```

The named command-line argument is either a misspelled option or a filename
in an unrecognized form (e.g., with no filename extension).

## **Error: Command-line argument '_arg_' is neither a recognized option nor a filename with a supported extension (_ext_).** {#cli_bad_option_legacy}

<!-- %check-cli -->
```bash
dafny zzz
```

The named command-line argument is either a misspelled option or a filename
in an unrecognized form (e.g., with no filename extension).

## **Error: '_name_': Filename extension '_ext_' is not supported. Input files must be Dafny programs (.dfy) or supported auxiliary files (_ext_)** {#cli_bad_extension}

<!-- %check-cli -->
```bash
dafny resolve z.zzz
```

Dafny programs are in files with a `.dfy` extension.
A Dafny program may be combined with other files appropriate to the
target programming language being used, such as `.dll` files for C#
or `.java` or `.jar` files for Java. The stated extension is not
recognized.





<!-- DafnyCore/DafnyOptions.cs -->

<!-- TODO: Errors in PrintMode? -->
<!-- TODO: Errors in diagnosticsFormat? -->

## Error: Invalid argument _argument_ to option _option_

<!-- %check-cli -->
```bash 
dafny resolve --function-syntax:2 mod.dfy
```

This is a generic error message about command-line arguments,
indicating that the value given (after the `:` or `=` or as the next command-line argument) is not recognized as a valid value for the given option.

The correct spellings of the valid values should be stated 
in the help document (`dafny -?` or `dafny <command> -h`).

## Error: Invalid argument _argument_ to option --quantifier-syntax

<!-- %check-cli -->
```bash 
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


<!-- Somewhere -->

## **Error: unknown switch: _switch_** {#cli_unknown_legacy_option}

<!-- %check-cli -->
```bash
dafny --stdin
```

This error results from using an unknown command-line option in the 
legacy CLI, such as one that begins with a double hyphen.
It is recommended to use the new CLI in which the command-line begins
with an action verb (e.g., resolve, verify, run) followed by 
files, folders, and options written with double=hyphen prefixes.
