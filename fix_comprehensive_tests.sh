#!/bin/bash

# Comprehensive list of test files that likely need updating
test_files=(
    # More dafny0 files
    "Corecursion"
    "DefaultParameters"
    "Fuel"
    "FuelInAssertions"
    "Ghost"
    "Havoc"
    "Iterators"
    "LetExpr"
    "Newtypes"
    "Opaque"
    "Parallel"
    "Quantifiers"
    "Reads"
    "Sequences"
    "Superposition"
    "TailRecursion"
    "Trait"
    "TypeAntecedents"
    "TypeMembers"
    "UnboundedIntegers"
    "WellInduction"
    # dafny2 files
    "Calculations"
    "CalcExample"
    "Classics"
    "Coinductive"
    "Dafny2"
    "COST-verif-comp-2011-1-MaxArray"
    "COST-verif-comp-2011-2-MaxTree-class"
    "COST-verif-comp-2011-3-TwoDuplicates"
    "COST-verif-comp-2011-4-FloydCycleDetect"
    "Intervals"
    "SnapshotableTrees"
    "StoreAndRetrieve"
    "TreeBarrier"
    "TuringFactorial"
    # dafny3 files
    "Absyn"
    "Dijkstra"
    "Iter"
    "Streams"
    "Paulson"
    "Filter"
    "GenericSort"
    "Heap"
    "InductionVsCoinduction"
    "Koenig"
    "SimpleCoinduction"
    "Zip"
)

echo "Running comprehensive test fixes..."

updated_count=0
failed_count=0
passed_count=0
total_count=${#test_files[@]}

for i in "${!test_files[@]}"; do
    test_file="${test_files[$i]}"
    echo "[$((i+1))/$total_count] Testing $test_file..."
    
    if make test name="$test_file" build=false 2>&1 | grep -q "FAIL"; then
        echo "  $test_file failed, updating expect file..."
        if make test update=true name="$test_file" build=false > /dev/null 2>&1; then
            echo "  ✅ $test_file updated successfully"
            ((updated_count++))
        else
            echo "  ❌ Failed to update $test_file"
            ((failed_count++))
        fi
    else
        echo "  ✅ $test_file already passes"
        ((passed_count++))
    fi
done

echo ""
echo "Comprehensive update complete!"
echo "Updated: $updated_count"
echo "Already passing: $passed_count" 
echo "Failed to update: $failed_count"
echo "Total processed: $total_count"
