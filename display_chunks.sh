#!/bin/bash

# Function to display output in chunks
display_chunks() {
  local file=$1
  local chunk_size=${2:-200}
  
  # Get total number of lines
  local total_lines=$(wc -l < "$file")
  local chunks=$(( (total_lines + chunk_size - 1) / chunk_size ))
  
  echo "File has $total_lines lines, displaying in $chunks chunks of $chunk_size lines each"
  
  for (( i=0; i<chunks; i++ )); do
    local start=$((i * chunk_size + 1))
    local end=$(((i + 1) * chunk_size))
    
    echo "=== Chunk $((i+1))/$chunks (lines $start-$end) ==="
    sed -n "${start},${end}p" "$file"
    
    if [[ $i -lt $((chunks-1)) ]]; then
      read -p "Press Enter to continue to next chunk..." 
    fi
  done
}

# Make the script executable
chmod +x display_chunks.sh
