#!/usr/bin/env python
"""
Simple driver around python's difflib that implements a basic ``diff`` like
tool. This exists to provide a simple ``diff`` like tool that will run on
Windows where only the ``fc`` tool is available.
"""
import argparse
import difflib
import os
import sys

def main(args):
    parser = argparse.ArgumentParser(formatter_class=argparse.RawDescriptionHelpFormatter,
                                     description=__doc__
                                    )
    # Open in binary mode so python doesn't try and do
    # universal line endings for us.
    parser.add_argument('from-file',
                        type=argparse.FileType('rb'),
                       )
    parser.add_argument('to-file',
                        type=argparse.FileType('rb'),
                       )
    parser.add_argument('-U','--unified=',
                        type=int,
                        default=3,
                        help='Number of context lines to show. '
                             'Default %(default)s'
                       )
    parser.add_argument('--strip-trailing-cr',
                        action='store_true',
                        help='strip trailing carriage return when comparing'
                       )
    parser.add_argument('--ignore-all-space','-w',
                        action='store_true',
                        help='Ignore all whitespace characters when comparing'
                       )

    parsedArgs = parser.parse_args(args)
    fromFile, fromFileName = preProcess(getattr(parsedArgs,'from-file'),
                                        parsedArgs.strip_trailing_cr,
                                        parsedArgs.ignore_all_space
                                       )
    toFile, toFileName = preProcess(getattr(parsedArgs,'to-file'),
                                    parsedArgs.strip_trailing_cr,
                                    parsedArgs.ignore_all_space
                                   )
    result = difflib.unified_diff(fromFile,
                                  toFile,
                                  fromFileName,
                                  toFileName,
                                  n=getattr(parsedArgs,'unified='),
                                 )
    # Force lazy computation to happen now
    result = list(result)

    if len(result) == 0:
        # Files are identical
        return 0
    else:
        for l in result:
            sys.stdout.write(l)
        return 1

def preProcess(openFile, stripTrailingCR=False, ignoreAllSpace=False):
    """
    Helper function to read lines in a file and do any necessary
    pre-processing
    """
    original = openFile.readlines()

    # Translation table deletes white space characters Note we don't remove
    # newline characters because this will create a mess when outputting the
    # diff. Is this the right behaviour?
    deleteChars=' \t'
    if sys.version_info.major  >= 3:
        translationTable = str.maketrans('','', deleteChars)

    copy = [ ]
    for line in original:
        newLine = str(line.decode())

        if stripTrailingCR:
            if newLine[-2:] == '\r\n' or newLine[-2:] == '\n\r':
                newLine = newLine[:-2] + '\n'

        if ignoreAllSpace:
            newLine = newLine.translate(translationTable)

        copy.append(newLine)

    return (copy, openFile.name)

def getFileName(openFile):
    return openFile.name

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))

