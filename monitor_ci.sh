#!/bin/bash

# CI Monitoring Script for PR 3324
# Usage: ./monitor_ci.sh [interval_minutes]

INTERVAL_MINUTES=${1:-10}
INTERVAL_SECONDS=$((INTERVAL_MINUTES * 60))
PR_NUMBER=3324

echo "Monitoring CI for PR $PR_NUMBER every $INTERVAL_MINUTES minutes..."
echo "Press Ctrl+C to stop monitoring"
echo ""

while true; do
    echo "=== $(date) ==="
    
    # Get CI status
    gh pr checks $PR_NUMBER
    
    echo ""
    echo "Waiting $INTERVAL_MINUTES minutes before next check..."
    echo ""
    
    sleep $INTERVAL_SECONDS
done
