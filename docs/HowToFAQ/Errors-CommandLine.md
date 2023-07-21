
<!-- %default %useHeadings %check-ids -->

<!-- DafnyDriver/DafnyDriver.cs -->

## **Error: No compiler found for target _target_; expecting one of _known_** {#cli_unknown_compiler}

<!-- %check-cli %err -->
```bash
dafny build -t:zzz
```

The `-t` or `--target` options specifies which backend compiler to use for 
those dafny commands that compile dafny to other programming languages. 
This error message says that the named language is not supported.

## **Error: No input files were specified in command-line _command_** {#cli_no_files}

<!-- %check-cli  %err-->
```bash
dafny resolve
```

Any valid dafny invocation requires at least one .dfy file. 
The only exceptions are the special commands like `--help` and `--version`.


## ***** Error: _file_: Central Directory corrupt.** {#cli_bad_doo}

<!-- %no-check --> <!-- TODO - not working on CI because of extra file -->
```bash
dafny resolve --use-basename-for-filename testsource/test1.dfy testsource/BadDoo.doo
```

This error message says that the `.doo` file was not able to be successfully unzipped.
It indicates that the file is either corrupted or misnamed (it should not be a .doo file).

## **Error: file _name_ not found** {#cli_file_not_found}

<!-- %check-cli -->
```bash
dafny build -t:java testfiles/a.dfy zzz.java
```

This error message simply states that the named file could not be found
by the dafny tool. Note that files on the command-line are named
relative to the current working directory of the shell in which the
command is invoked or are absolute file paths. In particular, this
instance of this error message identifies non-.dfy files that still
have permitted extensions (according to the target platform) but
cannot be found in the file system.

## **Error: Command-line argument '_arg_' is neither a recognized option nor a filename with a supported extension (_ext_).** {#cli_bad_option}

<!-- %check-cli -->
```bash
dafny resolve --zzz
```

The named command-line argument is either a misspelled option or a filename
in an unrecognized form (e.g., with no filename extension).
An invalid option with a filename as value can look like either one, such as `--out:a.doo`.

## **Error: unknown switch: -zzz** {#cli_bad_option_legacy}

<!-- %check-cli %err %first -->
```bash
dafny -zzz
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

<!--
## **Error: The command-line contains no .dfy files** {#cli-no-dafny-file_2}

 TODO - this appears to be no longer reachable -->

<!--
## **Error: The command-line contains no .dfy files** {#cli-no-dafny-folder}

 TODO - this appears to be no longer reachable -->

## **Error: Only one .dfy file can be specified for testing** {#cli-test-generation}

<!-- %no-check -->
```bash
dafny generate-tests block x.dfy y.dfy
```

The test-generation tool is still experimental.
However, it is expected to take just a single `.dfy` file as input.


## **Error: ModelView file must be specified when attempting counterexample extraction** {#cli-counterexample}

<!-- %no-check --> <!-- TODO - not working on CI because of extra file -->
```bash
dafny /extractCounterexample testsource/test1.dfy
```

When requesting a counterexample to be generated, some additional options must be specified:
a model view file using `/mv:<file>` and
`/proverOpt:O:model.completion=true` and
`/proverOpt:O:model_compress=false` (for z3 version < 4.8.7) or
`/proverOpt:O:model.compact=false `(for z3 version >= 4.8.7).

The model view file is an arbitrary non-existent file that is created and used as a temporary file
during the creation of the counterexamples.

## **Error: Feature not supported for this compilation target: _feature_** {#f_unsupported_feature}

<!-- %check-run %exit 3 %options -t:cpp --unicode-char=true -->
```dafny
method m() {}
```

The backends that Dafny supports have their own limitations on the ability to implement some of Dafny's features. 
This error message indicates that the Dafny program in question has hit one of these limitations. 
Some limitations are inherent in the language, but others are a question of implementation priorities to date.
If the feature is an important one for your project, communicate with the Dafny team to determine if the 
omission can be corrected.

## **Please use the '--check' and/or '--print' option as stdin cannot be formatted in place.** {#f_missing_format_option}

<!-- %check-cli %err %first -->
```bash
dafny format --stdin
```

The dafny `format` command formats its input dafny program. The default behavior is to format the input files
in place. It can instead just check that the file is formatted (`--check`) or print the formatted version to 
stdout (`--print`). If the `--stdin` option is used, the input dafny program is taken from stdin, in which case
it cannot be formatted in place, so either the `--check` or `--print` options must be used in conjunction with `--stdin`.

## **The file _file_ needs to be formatted** {#f_file_needs_formatting}

<!-- %check-cli -->
dafny format testsource/test2.dfy
-->

This message is not an error. Rather it is the expected output of the `dafny format` command when
`--check` is used: it states that the named input file is not formatted according to Dafny style.
You can use `--print` to see the output. Also for an input file `test.dfy`, the command
`dafny format --print test.dfy | diff test.dfy -` provides a diff between the original and the formatted files
(without making any changes).

<!-- DafnyCore/DafnyOptions.cs -->

## **Error: Invalid argument _argument_ to option print-mode_help_** {#cli_print_mode}

<!-- %check-cli %err %first -->
```bash 
dafny -printMode:zzz
```

The `printMode` option has a number of alternative values that are spelled out in the help document (`dafny -?`).
It is also recommended to use the new CLI, with the option `--print-mode`.

## **Error: Unsupported diagnostic format: _format_; expecting one of 'json', 'text'.** {#cli_diagnostic_format}

<!-- %check-cli %err %first -->
```bash
dafny /diagnosticsFormat:zzz
```

This option controls the format of error messages. Typically the 'text' format is used (and is the default).
But 'json' is also an option. Any other choice is illegal and results in this error message.

## **Error: Invalid argument _argument_ to option functionSyntax_help_** {#cli_function_syntax}

<!-- %check-cli %err %first -->
```bash 
dafny -functionSyntax:z
```

The `functionSyntax` option has a number of alternative values that are spelled out in the help document (`dafny -?`),
most commonly the values '3' and '4' ('4' for dafny version 4.0 and later).
It is also recommended to use the new CLI, with the option `--function-syntax`.

## **Error: Invalid argument _argument_ to option quantifierSyntax_help_** {#cli_quantifier_syntax}

<!-- %check-cli %err %first -->
```bash 
dafny -quantifierSyntax:z
```

The `quantifierSyntax ` option has a number of alternative values that are spelled out in the help document (`dafny -?`),
most commonly the values '3' and '4' ('4' for dafny version 4.0 and later).
It is also recommended to use the new CLI, with the option `--quantifier-syntax`.

## **Error: Invalid argument _argument_ to option verificationLogger_help_** {#cli_verification_logger}

<!-- %check-cli %err %first -->
```bash 
dafny -verificationLogger:z
```

The `verificationLogger` option has these alternatives: trx, csv, text.
The option name in the new CLI is `--log-format`.

## **Error: Invalid argument _argument_ to option testContracts_help_** {#cli_test_contracts}

<!-- %check-cli %err %first -->
```bash 
dafny -testContracts:z
```

The `testContracts` option has these alternatives: Externs, TestedExterns.
The similar option in the new CLI is `--test-assumptions`.

## **Error: Invalid argument _argument_ to option printIncludes_help_** {#cli_print_includes}

<!-- %check-cli %err %first -->
```bash 
dafny -printIncludes:z
```

The `printIncludes` option has these alternatives: None, Immediate, Transitive.

## **Argument '_argument_' not recognized. _Alternatives_** {#cli_quantifier_syntax}

<!-- %no-check TODO: Outputs the help document  -->
```bash 
dafny resolve --show-snippets:false --quantifier-syntax:2 null.dfy
```

This is a generic error message about command-line arguments,
indicating that the value given (after the `:` or `=` or as the next command-line argument) is not recognized as a valid value for the given option.

The correct spellings of the valid values should be stated 
in the help document (`dafny -?` or `dafny <command> -h`).


<!-- In boogie option processing -->

## **Error: unknown switch: _switch_** {#cli_unknown_legacy_option}

<!-- %check-cli %err %first -->
```bash
dafny --stdin
```

This error results from using an unknown command-line option in the 
legacy CLI, such as one that begins with a double hyphen.
It is recommended to use the new CLI in which the command-line begins
with an action verb (e.g., resolve, verify, run) followed by 
files, folders, and options written with double-hyphen prefixes.
