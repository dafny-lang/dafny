#!/usr/bin/env python3
import re
import sys
import difflib
import shutil

def extract_id(line):
    """Extract ID from a line containing {:id "idXXX"}"""
    match = re.search(r'{:id "id(\d+)"}', line)
    if match:
        return match.group(0), match.group(1)
    else:
        return None, None

def fix_id_discrepancies(file_to_modify, reference_file):
    # Create backup of the file to modify
    backup_file = file_to_modify + ".backup"
    shutil.copy2(file_to_modify, backup_file)
    print(f"Created backup at {backup_file}")
    
    # Read files
    with open(file_to_modify, 'r') as f:
        file_a_lines = f.readlines()
    with open(reference_file, 'r') as f:
        file_b_lines = f.readlines()
    
    # Get diff and filter out ? lines
    diff = [line for line in difflib.ndiff(file_a_lines, file_b_lines) if not line.startswith('? ')]
    
    # Process the diff and build modified lines in a single pass
    modified_lines = []
    i = 0
    changes_made = 0
    
    while i < len(diff):
        line = diff[i]
        
        if line.startswith('  '):  # Unchanged line
            modified_lines.append(line[2:])
            i += 1
            
        elif line.startswith('- '):  # Line from file A
            # Collect consecutive removed lines with IDs
            removed_lines = [line[2:]]
            removed_ids = []
            id_str, id_num = extract_id(line[2:])
            if id_str:
                removed_ids.append((id_str, id_num))
            
            # Collect more consecutive removed lines with IDs
            j = i + 1
            while j < len(diff) and diff[j].startswith('- '):
                removed_lines.append(diff[j][2:])
                id_str, id_num = extract_id(diff[j][2:])
                if id_str:
                    removed_ids.append((id_str, id_num))
                j += 1
            
            # Now look for consecutive added lines
            added_lines = []
            added_ids = []
            
            while j < len(diff) and diff[j].startswith('+ '):
                added_lines.append(diff[j][2:])
                id_str, id_num = extract_id(diff[j][2:])
                if id_str:
                    added_ids.append((id_str, id_num))
                j += 1
            
            # Check if we have matching number of lines with IDs
            if len(removed_ids) > 0 and len(removed_ids) == len(added_ids):
                # Check if lines are identical except for IDs
                can_replace_all = True
                for k in range(len(removed_lines)):
                    if k >= len(added_lines):
                        can_replace_all = False
                        break
                    
                    # If this line has an ID, check if it matches except for the ID
                    if k < len(removed_ids):
                        removed_without_id = removed_lines[k].replace(removed_ids[k][0], "ID_PLACEHOLDER")
                        added_without_id = added_lines[k].replace(added_ids[k][0], "ID_PLACEHOLDER")
                        if removed_without_id != added_without_id:
                            can_replace_all = False
                            break
                
                if can_replace_all:
                    # Replace IDs in the removed lines
                    for k in range(len(removed_ids)):
                        old_id_str, _ = removed_ids[k]
                        new_id_str, _ = added_ids[k]
                        modified_line = removed_lines[k].replace(old_id_str, new_id_str)
                        modified_lines.append(modified_line)
                        changes_made += 1
                        print(f"Changed ID: {old_id_str} -> {new_id_str}")
                    
                    # Skip ahead past all the lines we've processed
                    i = j
                    continue
            
            # If we couldn't replace all, just add the original lines
            for line in removed_lines:
                modified_lines.append(line)
            i = j
            
        elif line.startswith('+ '):  # Line only in file B
            # Skip lines that are only in file B
            i += 1
            
        else:  # Should not happen with difflib output
            i += 1
    
    # Write the modified file
    with open(file_to_modify, 'w') as f:
        f.writelines(modified_lines)
    
    if changes_made > 0:
        print(f"Modified {file_to_modify} with {changes_made} ID changes. Backup saved at {backup_file}")
    else:
        print(f"No ID changes made. Original file is unchanged.")

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python fix_id_discrepancies.py file_to_modify.bpl reference_file.bpl")
        sys.exit(1)
    
    file_to_modify = sys.argv[1]
    reference_file = sys.argv[2]
    
    fix_id_discrepancies(file_to_modify, reference_file)