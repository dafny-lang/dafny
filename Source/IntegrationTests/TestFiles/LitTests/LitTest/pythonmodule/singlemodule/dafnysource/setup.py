# setup.py
# installs the generated PythonModule1 as a Python module
from setuptools import setup

setup(
    name="testpythonmodulesinglemodule",
    version="0.1.0",
    packages=["PythonModule1"],
    python_requires='>=3.6',
    install_requires=[
        'DafnyRuntimePython',
    ],
)