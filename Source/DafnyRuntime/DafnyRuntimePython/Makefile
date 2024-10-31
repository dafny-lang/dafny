
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../Dafny --no-build --

GENERATED_SYSTEM_MODULE_SOURCE=../obj/systemModulePopulator-py/System_.py
GENERATED_SYSTEM_MODULE_TARGET=System_/__init__.py

# Use a virtual environment in order to avoid polluting the system installation,
# dependency conflicts, etc.
VIRTUALENV = venv
ifeq ($(OS),Windows_NT)
	VIRTUALENV_PYTHON = $(VIRTUALENV)/Scripts/python.exe
else
	VIRTUALENV_PYTHON = $(VIRTUALENV)/bin/python
endif

all: check-system-module

build-system-module:
	$(DAFNY) translate py --no-verify --use-basename-for-filename --system-module:OmitAllOtherModules ../systemModulePopulator.dfy --output:../obj/systemModulePopulator

check-system-module: build-system-module
	diff $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

update-system-module: build-system-module
	cp $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

setup-venv:
	python -m venv --clear $(VIRTUALENV)
	$(VIRTUALENV_PYTHON) -m pip install --upgrade build twine

clean-package:
	rm -rf dist/ *.egg-info/

build-package:
	$(VIRTUALENV_PYTHON) -m build

upload-package-testpypi:
	$(VIRTUALENV_PYTHON) -m twine upload --repository testpypi dist/*

upload-package-pypi:
	$(VIRTUALENV_PYTHON) -m twine upload dist/*
