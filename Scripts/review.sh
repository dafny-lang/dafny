#!/bin/bash
# Usage: ./review.sh [PR_NUMBER] [REPO] [FOCUS_AREAS]
# Example: ./review.sh 3324
# Example: ./review.sh 3324 dafny-lang/dafny "performance,security"
# Example: ./review.sh 3324 dafny-lang/dafny "breaking-changes"

PR_NUMBER=${1}
REPO=${2:-"dafny-lang/dafny"}
FOCUS_AREAS=${3:-"general"}

# Interactive PR number input if not provided
if [ -z "$PR_NUMBER" ]; then
    echo "Dafny PR Review Script v1.2.0"
    echo ""
    echo "Optional suggested focus areas:"
    echo "  - general"
    echo "  - performance"
    echo "  - security"
    echo "  - breaking-changes"
    echo "  - tests"
    echo "  - documentation"
    echo "  - error-handling"
    echo ""
    
    # Prompt for PR number
    read -p "Enter PR number: " PR_NUMBER
    
    if [ -z "$PR_NUMBER" ]; then
        echo "❌ Error: PR number is required"
        exit 1
    fi
    
    # Prompt for repository (with default)
    read -p "Enter repository [dafny-lang/dafny]: " input_repo
    if [ -n "$input_repo" ]; then
        REPO="$input_repo"
    fi
    
    # Prompt for focus areas (with default)
    read -p "Enter focus areas [general]: " input_focus
    if [ -n "$input_focus" ]; then
        FOCUS_AREAS="$input_focus"
    fi
    
    echo ""
fi

# Configuration
MAX_DIFF_LINES=500
SLEEP_BETWEEN_FILES=1

# Check for required dependencies
echo "🔧 Checking dependencies..."

# Check for GitHub CLI
if ! command -v gh &> /dev/null; then
    echo "❌ Error: GitHub CLI (gh) is not installed"
    echo "Please install it from: https://cli.github.com/"
    exit 1
fi

# Check for git
if ! command -v git &> /dev/null; then
    echo "❌ Error: git is not installed"
    echo "Please install git to continue"
    exit 1
fi

# Detect available AI tools
AI_TOOL=""
AI_COMMAND=""

if command -v q &> /dev/null; then
    AI_TOOL="q"
    AI_COMMAND="q chat --no-interactive"
    echo "✅ Found Q CLI for AI reviews"
elif command -v claude &> /dev/null; then
    AI_TOOL="claude"
    AI_COMMAND="claude"
    echo "✅ Found Claude CLI for AI reviews"
else
    echo "❌ Error: No AI tool found for code review"
    echo ""
    echo "Please install one of the following:"
    echo "  • Q CLI: https://github.com/qnguyen3/q"
    echo "  • Claude CLI: https://github.com/anthropics/claude-cli"
    echo ""
    echo "Or install via package managers:"
    echo "  • npm install -g @anthropic-ai/claude-cli"
    echo "  • pip install q-cli"
    echo ""
    exit 1
fi

# Check GitHub CLI authentication
if ! gh auth status &> /dev/null; then
    echo "❌ Error: GitHub CLI is not authenticated"
    echo "Please run: gh auth login"
    exit 1
fi

echo "✅ All dependencies satisfied"

echo "🔍 Reviewing PR #$PR_NUMBER from $REPO..."
echo "📋 Focus areas: $FOCUS_AREAS"

# Create temporary directory
TEMP_DIR=$(mktemp -d)
cd "$TEMP_DIR"

# Clone the repository and get PR info
echo "📥 Fetching PR information..."
gh repo clone "$REPO" .
gh pr checkout "$PR_NUMBER"

# Get PR description
echo "📋 Fetching PR description..."
gh pr view "$PR_NUMBER" --json body -q .body > pr_description.txt

# Get the base branch for comparison
BASE_BRANCH=$(gh pr view "$PR_NUMBER" --json baseRefName -q .baseRefName)
echo "📊 Comparing against base branch: $BASE_BRANCH"

# Use local git to get changed files, filtering out delete/add pairs
echo "📋 Getting list of changed files using local git..."
git diff --name-status "$BASE_BRANCH"...HEAD > all_changes.txt

# Process changes to handle delete/add pairs that should cancel out
echo "🔄 Processing changes to handle delete/add pairs..."
awk '
BEGIN { 
    # Track file statuses
}
{
    file = $2
    status = $1
    
    if (status == "D") {
        deleted[file] = 1
    } else if (status == "A") {
        added[file] = 1
    } else {
        # Modified, renamed, etc. - keep as-is
        other[file] = status
    }
}
END {
    # Output files that are truly changed
    for (file in other) {
        print other[file] "\t" file
    }
    
    # Output additions that dont have corresponding deletions
    for (file in added) {
        if (!(file in deleted)) {
            print "A\t" file
        }
    }
    
    # Output deletions that dont have corresponding additions
    for (file in deleted) {
        if (!(file in added)) {
            print "D\t" file
        }
    }
    
    # Files that were both deleted and added are considered "recreated" - treat as modified
    for (file in deleted) {
        if (file in added) {
            print "M\t" file
        }
    }
}
' all_changes.txt | sort -k2 > filtered_changes.txt

# Extract just the filenames for processing
awk '{print $2}' filtered_changes.txt > changed_files.txt

total_files=$(wc -l < changed_files.txt)
echo "📁 Total files changed (after filtering delete/add pairs): $total_files"

# Initialize counters
violations=0
files_processed=0
passed_files=0
failed_files=0
skipped_files=0

# Time tracking for estimation
start_time=$(date +%s)
first_file_completed=false

# Track failed files for status display
declare -a failed_file_list
declare -a failed_reason_list

echo ""
echo "🤖 Starting code review (only showing files that need human attention)..."

# Function to clear current line properly
clear_line() {
    printf "\r\033[K"
}

# Function to display 2D status view
show_status_view() {
    local current=$1
    local total=$2
    local current_file=$3
    
    # Clear screen and move to top
    printf "\033[2J\033[H"
    
    echo "========================================="
    echo "Current review concerns:"
    
    if [ ${#failed_file_list[@]} -eq 0 ]; then
        echo "  (No issues found so far)"
    else
        for i in "${!failed_file_list[@]}"; do
            echo "  ${failed_file_list[$i]}: ${failed_reason_list[$i]}"
        done
    fi
    
    echo ""
    echo "Progress:"
    echo "  $((current - 1))/$total files reviewed so far"
    echo "  Currently reviewing: $current_file"
    echo "========================================="
    echo ""
}

# Function to format time duration
format_time() {
    local seconds=$1
    if [ $seconds -lt 60 ]; then
        echo "${seconds}s"
    elif [ $seconds -lt 3600 ]; then
        local minutes=$((seconds / 60))
        local remaining_seconds=$((seconds % 60))
        echo "${minutes}m ${remaining_seconds}s"
    else
        local hours=$((seconds / 3600))
        local remaining_minutes=$(((seconds % 3600) / 60))
        echo "${hours}h ${remaining_minutes}m"
    fi
}

# Function to display truncated progress with time estimation
show_progress() {
    local current=$1
    local total=$2
    local file=$3
    
    # Truncate filename if too long (keep last 50 chars)
    local display_file="$file"
    if [ ${#file} -gt 50 ]; then
        display_file="...${file: -47}"
    fi
    
    # Calculate time estimation after first file
    local time_info=""
    if [ "$first_file_completed" = true ] && [ $current -gt 1 ]; then
        local current_time=$(date +%s)
        local elapsed=$((current_time - start_time))
        local analyzed_files=$((current - skipped_files))
        
        if [ $analyzed_files -gt 0 ]; then
            local avg_time_per_file=$((elapsed / analyzed_files))
            local remaining_files=$((total - current))
            local estimated_remaining=$((remaining_files * avg_time_per_file))
            
            local elapsed_formatted=$(format_time $elapsed)
            local remaining_formatted=$(format_time $estimated_remaining)
            time_info=" | ⏱️ ${elapsed_formatted} elapsed, ~${remaining_formatted} left"
        fi
    fi
    
    # Create progress line and truncate if needed
    local progress_line="🔎 [$current/$total] Reviewing: $display_file$time_info"
    local term_width=$(tput cols 2>/dev/null || echo 80)
    
    if [ ${#progress_line} -gt $term_width ]; then
        # Try to fit by shortening filename first
        local max_file_len=$((term_width - 25 - ${#time_info}))
        if [ $max_file_len -gt 10 ]; then
            display_file="...${file: -$((max_file_len - 3))}"
            progress_line="🔎 [$current/$total] Reviewing: $display_file$time_info"
        fi
        
        # If still too long, truncate time info
        if [ ${#progress_line} -gt $term_width ]; then
            progress_line="🔎 [$current/$total] Reviewing: $display_file"
        fi
    fi
    
    # Ensure we don't exceed terminal width to prevent line wrapping
    if [ ${#progress_line} -gt $term_width ]; then
        progress_line="${progress_line:0:$((term_width-1))}"
    fi
    
    printf "\r\033[K%s" "$progress_line"
}

# Loop through each changed file
while IFS= read -r file; do
    files_processed=$((files_processed + 1))
    
    # Show current status view
    show_status_view $files_processed $total_files "$file"
    
    # Skip binary files and other files that don't need review
    if [[ "$file" =~ \.(png|jpg|jpeg|gif|bmp|ico|svg|pdf|zip|tar|gz|bz2|xz|7z|rar|dll|exe|pdb|bin|so|dylib|jar|class|war|ear|deb|rpm|dmg|pkg|msi|woff|woff2|ttf|otf|eot)$ ]]; then
        skipped_files=$((skipped_files + 1))
        continue
    fi
    
    # Skip generated files, build artifacts, and common ignore patterns
    if [[ "$file" =~ (node_modules/|\.git/|build/|dist/|target/|bin/|obj/|\.vscode/|\.idea/|\.vs/|packages/|\.nuget/|TestResults/|coverage/|\.nyc_output/) ]]; then
        skipped_files=$((skipped_files + 1))
        continue
    fi
    
    # Skip lock files and other generated files
    if [[ "$file" =~ (package-lock\.json|yarn\.lock|Pipfile\.lock|poetry\.lock|Gemfile\.lock|composer\.lock|\.min\.js|\.min\.css)$ ]]; then
        skipped_files=$((skipped_files + 1))
        continue
    fi
    
    # Skip files that don't exist (might have been deleted)
    if [ ! -f "$file" ]; then
        skipped_files=$((skipped_files + 1))
        continue
    fi
    
    # Get the diff for this specific file using local git
    git diff "$BASE_BRANCH"...HEAD -- "$file" > "file_diff_$files_processed.txt"
    
    # Check if file has any actual changes
    if [ ! -s "file_diff_$files_processed.txt" ]; then
        skipped_files=$((skipped_files + 1))
        continue
    fi
    
    diff_lines=$(wc -l < "file_diff_$files_processed.txt")
    
    # Review function that handles a diff chunk
    review_diff_chunk() {
        local file="$1"
        local focus="$2"
        local diff_content="$3"
        local chunk_num="$4"
        local total_chunks="$5"
        local chunk_id="${files_processed}_${chunk_num}"
        
        cat > "prompt_${chunk_id}.txt" << EOF
Review this Dafny PR change. Focus: $focus

FILE: $file $([ $total_chunks -gt 1 ] && echo "(Part $chunk_num of $total_chunks)")

DIFF:
$diff_content

Check for:
- Code quality issues
- Potential bugs
- Breaking changes
- Performance concerns

Respond with either:
<pass>Changes look good</pass>
OR
<fail>filename.ext: brief description of issues</fail>
EOF
        
        # Invoke AI tool for this chunk with timeout
        if [ "$AI_TOOL" = "q" ]; then
            timeout 300 bash -c "cat 'prompt_${chunk_id}.txt' | q chat --no-interactive" > "output_${chunk_id}.txt" 2>&1
            ai_exit_code=$?
        elif [ "$AI_TOOL" = "claude" ]; then
            timeout 300 bash -c "cat 'prompt_${chunk_id}.txt' | $AI_COMMAND" > "output_${chunk_id}.txt" 2>&1
            ai_exit_code=$?
        fi
        
        # Check if AI tool timed out or failed
        if [ $ai_exit_code -eq 124 ]; then
            echo "<fail>$file: AI tool timed out after 5 minutes</fail>" > "output_${chunk_id}.txt"
        elif [ $ai_exit_code -ne 0 ]; then
            echo "<fail>$file: AI tool failed with exit code $ai_exit_code</fail>" > "output_${chunk_id}.txt"
        fi
        
        # Return the output file path for processing
        echo "output_${chunk_id}.txt"
    }
    
    # Check if diff needs to be chunked
    if [ $diff_lines -gt $MAX_DIFF_LINES ]; then
        # Split large diff into chunks
        total_chunks=$(( (diff_lines + MAX_DIFF_LINES - 1) / MAX_DIFF_LINES ))
        chunk_outputs=()
        
        for ((chunk=1; chunk<=total_chunks; chunk++)); do
            start_line=$(( (chunk - 1) * MAX_DIFF_LINES + 1 ))
            end_line=$(( chunk * MAX_DIFF_LINES ))
            
            # Extract chunk content
            chunk_content=$(sed -n "${start_line},${end_line}p" "file_diff_$files_processed.txt")
            
            # Review this chunk
            output_file=$(review_diff_chunk "$file" "$FOCUS_AREAS" "$chunk_content" "$chunk" "$total_chunks")
            chunk_outputs+=("$output_file")
            
            sleep $SLEEP_BETWEEN_FILES
        done
        
        # Combine results from all chunks
        combined_output="output_$files_processed.txt"
        echo "COMBINED REVIEW RESULTS FOR: $file" > "$combined_output"
        echo "========================================" >> "$combined_output"
        
        chunk_passed=0
        chunk_failed=0
        
        for output_file in "${chunk_outputs[@]}"; do
            echo "" >> "$combined_output"
            cat "$output_file" >> "$combined_output"
            echo "" >> "$combined_output"
            
            if grep -q "<pass>" "$output_file"; then
                chunk_passed=$((chunk_passed + 1))
            elif grep -q "<fail>" "$output_file"; then
                chunk_failed=$((chunk_failed + 1))
            fi
        done
        
        # Determine overall result
        if [ $chunk_failed -gt 0 ]; then
            echo "<fail>$file: Issues found in $chunk_failed of $total_chunks chunks</fail>" >> "$combined_output"
        else
            echo "<pass>All $total_chunks chunks passed review</pass>" >> "$combined_output"
        fi
        
    else
        # Single review for small files
        diff_content=$(cat "file_diff_$files_processed.txt")
        review_diff_chunk "$file" "$FOCUS_AREAS" "$diff_content" "1" "1" > /dev/null
        cp "output_${files_processed}_1.txt" "output_$files_processed.txt"
    fi
    
    # Parse combined output
    if grep -q "<pass>" "output_$files_processed.txt"; then
        passed_files=$((passed_files + 1))
    elif grep -q "<fail>" "output_$files_processed.txt"; then
        # Extract failure reason from the fail tag
        fail_content=$(grep -o '<fail>.*</fail>' "output_$files_processed.txt" | sed 's/<fail>\(.*\)<\/fail>/\1/')
        
        # Add to failed files list
        failed_file_list+=("$file")
        failed_reason_list+=("$fail_content")
        
        failed_files=$((failed_files + 1))
        violations=$((violations + 1))
        
        # Update status display
        show_status_view $files_processed $total_files "$file"
    else
        # Missing XML tag
        failed_file_list+=("$file")
        failed_reason_list+=("Missing XML tag in AI response")
        
        violations=$((violations + 1))
        failed_files=$((failed_files + 1))
        
        # Update status display
        show_status_view $files_processed $total_files "$file"
    fi
    
    # Mark first file as completed for time estimation
    if [ "$first_file_completed" = false ]; then
        first_file_completed=true
    fi
    

    
    # Small delay to avoid overwhelming the APIecho "Hello, can you respond?" | q chat
    sleep $SLEEP_BETWEEN_FILES
    
done < changed_files.txt

# Final status display
printf "\033[2J\033[H"
echo "========================================="
echo "📊 FINAL CODE REVIEW SUMMARY"
echo "========================================="
echo ""
echo "Files processed: $files_processed"
echo "Files analyzed: $((files_processed - skipped_files))"
echo "Files skipped: $skipped_files"
echo "Files passed: $passed_files"
echo "Files failed: $failed_files"
echo ""

if [ $violations -eq 0 ]; then
    echo "✅ All analyzed files passed code review!"
    echo "✅ PR #$PR_NUMBER looks good to merge"
    exit_code=0
else
    echo "❌ Issues found in $violations file(s):"
    echo ""
    for i in "${!failed_file_list[@]}"; do
        echo "  ${failed_file_list[$i]}: ${failed_reason_list[$i]}"
    done
    echo ""
    echo "❌ Consider addressing these concerns before merging"
    exit_code=1
fi

# Cleanup
cd /
rm -rf "$TEMP_DIR"

echo "🎉 Code review complete!"
exit $exit_code
