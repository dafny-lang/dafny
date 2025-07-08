#!/bin/bash

# Wait for new CI to start and monitor it
set -e

echo "Waiting for new CI to start after our latest push..."

# Get the latest commit hash
latest_commit=$(git rev-parse HEAD)
echo "Latest commit: $latest_commit"

# Wait for new CI runs to appear
max_wait=300  # 5 minutes
wait_time=0
check_interval=30

while [ $wait_time -lt $max_wait ]; do
    echo "Checking for new CI runs... (waited ${wait_time}s)"
    
    # Check if there are any newer CI runs
    # This is a simple approach - in practice we'd check timestamps
    current_status=$(gh pr checks 3324 --json state,name | jq -r '.[] | .state' | sort | uniq -c)
    echo "Current CI status summary:"
    echo "$current_status"
    
    # Check if we have any running/pending jobs (indicating new CI)
    if echo "$current_status" | grep -q "PENDING\|IN_PROGRESS\|QUEUED"; then
        echo "New CI detected! Monitoring progress..."
        break
    fi
    
    sleep $check_interval
    wait_time=$((wait_time + check_interval))
done

if [ $wait_time -ge $max_wait ]; then
    echo "No new CI detected within timeout. Current status:"
    gh pr checks 3324 --json state,name | jq -r '.[] | "\(.state): \(.name)"' | sort | uniq -c
else
    echo "Monitoring new CI run..."
    # Wait for completion
    while true; do
        status=$(gh pr checks 3324 --json state | jq -r '.[] | .state' | sort -u)
        echo "CI status: $status"
        
        if ! echo "$status" | grep -q "PENDING\|IN_PROGRESS\|QUEUED"; then
            echo "CI completed!"
            break
        fi
        
        sleep 60
    done
    
    # Show final results
    echo "Final CI results:"
    gh pr checks 3324 --json state,name | jq -r '.[] | "\(.state): \(.name)"' | sort | uniq -c
fi
