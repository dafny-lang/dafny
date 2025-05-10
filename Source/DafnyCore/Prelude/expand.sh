#!/bin/bash

if [ "$#" -ne 2 ]; then
    echo "Usage: $0 input_file output_file"
    exit 1
fi

input_file="$1"
output_file="$2"

if [ ! -f "$input_file" ]; then
    echo "Error: Input file '$input_file' does not exist"
    exit 1
fi

# Get the directory of the input file
input_dir=$(dirname "$input_file")

while IFS= read -r line; do
    if [[ $line =~ ^#include[[:space:]]*\"([^\"]+)\" ]]; then
        # If line contains #include "file.h", include the file
        included_file="${BASH_REMATCH[1]}"
        # Look for the included file relative to the input file's directory
        full_path="$input_dir/$included_file"
        if [ -f "$full_path" ]; then
            cat "$full_path"
        else
            echo "Warning: Included file '$full_path' not found" >&2
        fi
    else
        # Otherwise print the line as-is
        echo "$line"
    fi
done < "$input_file" > "$output_file"