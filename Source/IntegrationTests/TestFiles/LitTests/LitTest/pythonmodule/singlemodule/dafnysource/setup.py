# setup.py
# installs the generated PythonModule1 as a Python module
from setuptools import setup

setup(
    name="testpythonmodulesinglemodule",
    version="0.1.0",
    packages=["PythonModule1"],
    description="A simple example Python module",
    author="Your Name",
    author_email="your.email@example.com",
    classifiers=[
        "Programming Language :: Python :: 3",
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
    ],
    python_requires='>=3.6',
)