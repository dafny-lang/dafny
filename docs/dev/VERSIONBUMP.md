# Change version number

After each release, we change the version number by first running

    python3 Scripts/prepare_release.py NEXT_VERSION set-next-version

where NEXT_VERSION is the version of the last release of the format
`major.minor.patch` and the patch has been increased by 1. This script
has for effect to change the version number in `Source/Directory.Build.props`.
Then, many things in Dafny that depend on this version number have to be
updated.

This file is an exhaustive list of everything that needs to be updated
whenever the version number changes. All these steps are
executable by running

    ./Scripts/bump_version_number.js NEW_VERSION

and `make bumpversion-test` run by the CI on each release
verifies that this file is in sync with that script.

# How to keep Dafny consistent with the new version number

Assuming `<TestDirectory>` to be `Source/IntegrationTests/TestFiles/LitTests/LitTest`,
perform the following:
* Update standard library doo files instead of rebuilding to avoid Z3 timeout issues
* In the test directory `Source/IntegrationTests/TestFiles/LitTests/LitTest`,
* Update test doo files instead of rebuilding
  * Update `pythonmodule/multimodule/PythonModule1.doo` version
  * Update `pythonmodule/nestedmodule/SomeNestedModule.doo` version
  * Update `gomodule/multimodule/test.doo` version
  * Search for `dafny_version = ` in checked-in `.dtr` files of the `<TestDirectory>`
   and update the version number.
    Except for the file NoGood.dtr which is not valid.
    Except for WrongDafnyVersion.dtr as well.
  * Update `comp/separate-compilation/translation-records/InvalidFormat.dfy.expect` by updating the version number after `by Dafny ` 
* In `Source/DafnyRuntime/DafnyRuntimeJava/build.gradle`, search for `version = ` and update the version number
* In `Source/DafnyRuntime/DafnyRuntimePython/pyproject.toml`, search for `version = ` and update the version number
* Update the Dafny runtime version number by searching for `DafnyRuntime-` and updating the version right afterwards, in the files `DafnyPipeline.csproj` and `DafnyRuntime.csproj`