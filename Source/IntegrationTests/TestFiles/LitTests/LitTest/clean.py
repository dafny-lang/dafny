#!/usr/bin/env python
"""
This is a convenient script to delete temporary files created by the lit and
legacy testing infrastructure. Both systems use the same name for Output
unfortunately so this script needs to be run before switching to the other
infrastructure.
"""
import logging
import os
import shutil
import sys

_name = 'Output'

def main():
    logging.basicConfig(level=logging.INFO)
    root = os.path.abspath(os.path.dirname(__file__))
    logging.info('Cleaning "{}"'.format(root))
    count = 0

    for (dirpath, dirnames, filenames) in os.walk(root):
        rmpath = os.path.join(dirpath, _name)
        if _name in dirnames:
            logging.info('Deleting lit temporary directory "{}"'.format(rmpath))
            shutil.rmtree(rmpath)
            count += 1
        elif _name in filenames:
            logging.info('Deleting batch testing output file "{}"'.format(os.path.join(dirpath, _name)))
            os.remove(rmpath)
            count += 1

    logging.info('\n\nDONE: Removed {}'.format(count))

if __name__ == '__main__':
    sys.exit(main())
