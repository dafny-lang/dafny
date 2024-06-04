# setup.py
# installs the committed PythonModule1 and generated PythonModule2 as a Python module
from setuptools import setup

setup(
    name="testpythonmodulemultimodule",
    version="0.1.0",
    packages=["PythonModule1", "PythonModule2"],
    python_requires='>=3.6',
    install_requires=[
        'DafnyRuntimePython',
    ],
)