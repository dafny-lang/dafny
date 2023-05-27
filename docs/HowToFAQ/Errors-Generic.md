<!-- %default %useHeadings -->

<!-- DafnyCore/Generic/Reporting.cs -->

## **Error: the included file _file_ contains error(s)** {#g_include_file_has_errors}

<!-- %no-check TODO - infrstructure does not handle examples with multiple errors -->
```dafny
include "testsource/TestA.dfy"
```

This error is shown when parsing a file A that includes another file B when B has errors of its own.
Without this message it can be easy to miss the fact that other errors in A are in fact caused
by errors in B. Some of the error messages shown may pertain to B rather than to A.
