
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../Dafny --no-build --

GENERATED_SYSTEM_MODULE_SOURCE=../obj/systemModulePopulator-py/System_.py
GENERATED_SYSTEM_MODULE_TARGET=src/System_/__init__.py

VIRTUALENV = venv

all: check-system-module

build-system-module:
	$(DAFNY) translate py --no-verify --use-basename-for-filename --system-module:OmitAllOtherModules ../systemModulePopulator.dfy --output:../obj/systemModulePopulator

check-system-module: build-system-module
	diff $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

update-system-module: build-system-module
	cp $(GENERATED_SYSTEM_MODULE_SOURCE) $(GENERATED_SYSTEM_MODULE_TARGET)

setup-venv:
	python -m venv --clear $(VIRTUALENV)
	$(VIRTUALENV)/bin/pip install --upgrade build twine

clean-package:
	rm -rf dist/

build-package:
	$(VIRTUALENV)/bin/python -m build

upload-package-testpypi:
	$(VIRTUALENV)/bin/python -m twine upload --repository testpypi dist/*

upload-package-pypi:
	$(VIRTUALENV)/bin/python -m twine upload dist/*
