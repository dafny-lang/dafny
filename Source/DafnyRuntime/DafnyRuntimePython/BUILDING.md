# Building the DafnyRuntimePython

## Prerequisites

- the `dotnet` CLI, to build Dafny
- Python, to build and upload the package
- [TestPyPI credentials](https://packaging.python.org/en/latest/guides/using-testpypi/), if you will upload to TestPyPI
- PyPI credentials, if you will upload to PyPI

## Steps

1. Ensure that the `System_` module is up-to-date:

```bash
# Ensure that the Dafny build is up-to-date,
# as it will be used to compile the System_ module.
$ dotnet build --project ../../Dafny

# Compile the System_ runtime module.
$ make update-system-module
```

2. Build the distribution package:

```bash
# Set up the build tooling
$ make setup-venv

# Remove old build artifacts
$ make clean-package

# Build the distribution package
$ make build-package
```

3. Check that the distribution package looks right locally and on TestPyPI,
   as (production) PyPI does not allow overwriting uploaded packages:

```bash
# List the distribution package's files, and check that:
#  1. the version number is correct
#  2. the `System_/__init__.py` file exists
#  3. the `dafny/__init__.py` file exists
$ tar tf dist/dafnyruntimepython-X.Y.Z.tar.gz

# Upload to TestPyPI, and check that it appears correct at
# <https://test.pypi.org/project/DafnyRuntimePython/>.
$ make upload-package-testpypi
```

4. Upload to PyPI:

```bash
$ make upload-package-pypi
```

You can view the uploaded package at <https://pypi.org/project/DafnyRuntimePython/>.

## More info

The packaging process is described in
<https://packaging.python.org/en/latest/tutorials/packaging-projects/>
