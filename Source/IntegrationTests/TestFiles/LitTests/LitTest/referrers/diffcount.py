#!/usr/bin/env python3
import sys
import difflib

def count_differences(file1, file2):
    # Read files
    with open(file1, 'r') as f:
        file1_lines = f.readlines()
    with open(file2, 'r') as f:
        file2_lines = f.readlines()
    
    # Get diff and filter out ? lines
    diff = [line for line in difflib.ndiff(file1_lines, file2_lines) if not line.startswith('? ')]
    
    # Count lines that start with + or -
    diff_count = sum(1 for line in diff if line.startswith('+ ') or line.startswith('- '))
    
    return diff_count

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python diffcount.py file1.bpl file2.bpl")
        sys.exit(1)
    
    file1 = sys.argv[1]
    file2 = sys.argv[2]
    
    count = count_differences(file1, file2)
    print(count)