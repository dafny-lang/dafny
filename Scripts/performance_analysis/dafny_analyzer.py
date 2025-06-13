#!/usr/bin/env python3
"""
Unified CLI for Dafny analysis tools.
"""
import argparse
from pathlib import Path
from sys import maxsize
from typing import List, Tuple, Dict, Any, Optional, Counter as CounterType
import numpy as np
from statistics import fmean, stdev
from collections import Counter
import csv
import re
import matplotlib
import matplotlib.pyplot as plt
from matplotlib.backends.backend_pdf import PdfPages

# Pre-compile regex patterns
LABEL_CHARS = r'\w\-: #\[\]\(\).@<>,?{}'
QI_PATTERN = re.compile(fr'\((\'[{LABEL_CHARS}]+\'|\"[{LABEL_CHARS}\']+\"), (\d+)\)')
QI_NAME_PATTERN = re.compile(fr"\[([{LABEL_CHARS}]+)\] ")

csv.field_size_limit(maxsize)

def read_and_filter_file(file_path: str) -> Tuple[List[str], List[List[str]], Dict[str, int]]:
    """Read a CSV file, get column indices, and filter out invalid data."""
    # Read CSV file
    with open(file_path, 'r') as f:
        data = list(csv.reader(f))
    header, data = data[0], data[1:]
    
    # Get indices of important columns from the header
    indices: Dict[str, int] = {}
    for column_name in ["crash", "p_crash", "timeout", "qi", "qi_top", "qi_dummys",
                "qi_dummy_top", "qi_top_names", "total_time"]:
        if column_name in header:
            indices[column_name] = header.index(column_name)
    
    # Filter out crashed and timed out entries
    filtered_data: List[List[str]] = data
    
    if "crash" in indices:
        filtered_data = [row for row in filtered_data if row[indices["crash"]] == "False"]

    if "p_crash" in indices:
        filtered_data = [row for row in filtered_data if row[indices["p_crash"]] == "False"]

    if "timeout" in indices:
        filtered_data = [row for row in filtered_data if row[indices["timeout"]] == "False"]
    
    return header, filtered_data, indices

def analyze_qi(stats: List[str], count: Optional[int] = None) -> List[Tuple[str, int]]:
    """Analyze quantifier instantiations and return the most common ones with counts."""
    aggregate: CounterType[str] = Counter()

    for stat_entry in stats:
        parsed_entries: List[Tuple[str, str]] = QI_PATTERN.findall(stat_entry)

        for name_orig, count_str in parsed_entries:
            name: str = name_orig[1:-1]  # Remove quotes
            match: Optional[re.Match] = QI_NAME_PATTERN.search(name)
            if match is not None and match.group(1) != "user_defined_quant":
                name = match.group(1)
            aggregate[name] += int(count_str)

    return aggregate.most_common(count)

def compute_swaps(bench: List[str], file: List[str]) -> Optional[int]:
    """Compute the number of swaps needed to transform file into bench."""
    swaps: int = 0
    file_copy: List[str] = file.copy()  # Work on a copy to avoid modifying the original

    for bench_idx in range(len(bench)):
        try:
            file_idx = file_copy.index(bench[bench_idx])
        except ValueError:
            return None  # Item not found

        if file_idx < bench_idx:
            return None  # Impossible to sort
        elif bench_idx == file_idx:
            continue

        assert bench_idx < file_idx
        swaps += file_idx - bench_idx
        del file_copy[file_idx]
        file_copy.insert(bench_idx, bench[bench_idx])

    return swaps

def extract_basic_data(data: List[List[str]], indices: Dict[str, int]) -> List[Tuple[str, str, str, str]]:
    """Extract basic data (filename, total_time, qi, qi_top_names) from filtered data."""
    result: List[Tuple[str, str, str, str]] = []
    for row in data:
        filename = row[0]
        total_time = row[indices.get("total_time", 0)]
        qi = row[indices.get("qi", 0)]
        qi_top_names = row[indices.get("qi_top_names", 0)]
        result.append((filename, total_time, qi, qi_top_names))

    result.sort(key=lambda e: e[0])  # Sort by filename
    return result

def compute_stats(benchmark_data: List[Tuple[str, str, str, str]],
                 file_data: List[Tuple[str, str, str, str]]) -> Tuple[float, float, int, Optional[int]]:
    """Compute statistics comparing benchmark data with file data."""
    bench_total_time: float = 0.0
    file_total_time: float = 0.0
    bench_qi: int = 0
    file_qi: int = 0
    regressions: int = 0
    processed_count: int = 0
    benchmark_idx: int = 0
    file_idx: int = 0

    bench_top_names: List[str] = []
    file_top_names: List[str] = []

    while benchmark_idx < len(benchmark_data) or file_idx < len(file_data):
        processed_count = processed_count + 1
        if not benchmark_idx < len(benchmark_data) or (file_idx < len(file_data) and file_data[file_idx][0] < benchmark_data[benchmark_idx][0]):
            file_idx += 1
        elif not file_idx < len(file_data) or (benchmark_idx < len(benchmark_data) and benchmark_data[benchmark_idx][0] < file_data[file_idx][0]):
            benchmark_idx += 1
            regressions = regressions + 1
        else:
            assert benchmark_data[benchmark_idx][0] == file_data[file_idx][0], f"{benchmark_data[benchmark_idx][0]}, {file_data[file_idx][0]}, {benchmark_idx}, {file_idx}"
            bench_total_time += float(benchmark_data[benchmark_idx][1])
            file_total_time += float(file_data[file_idx][1])
            bench_qi += int(benchmark_data[benchmark_idx][2])
            file_qi += int(file_data[file_idx][2])
            bench_top_names.append(benchmark_data[benchmark_idx][3])
            file_top_names.append(file_data[file_idx][3])
            benchmark_idx += 1
            file_idx += 1

    runtime_change: float = (file_total_time - bench_total_time) / bench_total_time * 100 if bench_total_time > 0 else 0
    qi_change: float = (file_qi - bench_qi) / bench_qi * 100 if bench_qi > 0 else 0

    swaps = compute_swaps([name for name, _ in analyze_qi(bench_top_names, 20)],
                   [name for name, _ in analyze_qi(file_top_names)])

    return runtime_change, qi_change, regressions, swaps

def analyze_correlations(header: List[str], data: List[List[str]], indices: Dict[str, int],
                     plot_output: Optional[str] = None, interactive: bool = False) -> None:
    """Analyze correlations in the data."""
    numeric_data: List[List[float]] = []
    rlabels: List[str] = []

    # Remove non-numeric columns
    skip_indices: List[int] = [0]  # Skip filename
    if "crash" in indices:
        skip_indices.append(indices["crash"])
    if "p_crash" in indices:
        skip_indices.append(indices["p_crash"])
    if "timeout" in indices:
        skip_indices.append(indices["timeout"])
    if "qi_top_names" in indices:
        skip_indices.append(indices["qi_top_names"])

    for col_idx, column_name in enumerate(header):
        if col_idx not in skip_indices:
            rlabels.append(column_name)

    # Convert to numeric data
    for row in data:
        numeric_row: List[float] = []
        for col_idx, value in enumerate(row):
            if col_idx not in skip_indices:
                try:
                    numeric_row.append(float(value))
                except ValueError:
                    numeric_row.append(0.0)
        numeric_data.append(numeric_row)

    # Calculate correlations with error handling
    numeric_data_array: np.ndarray = np.array(numeric_data, dtype=float)

    # Handle potential division by zero or NaN values
    with np.errstate(divide='ignore', invalid='ignore'):
        correlation_matrix = np.corrcoef(numeric_data_array, rowvar=False)
        # Replace NaN values with 0 (no correlation)
        correlation_matrix = np.nan_to_num(correlation_matrix)

    print("\n=== CONCENTRATION STATISTICS ===")
    print("The average qi_concentration is " + str(np.mean(numeric_data_array[:, rlabels.index("qi_concentration")])))
    print("The average qi_dummy_concentration is " + str(np.mean(numeric_data_array[:, rlabels.index("qi_dummy_concentration")])))

    # Print time correlations
    if "time" in rlabels:
        print("\n=== TIME CORRELATIONS ===")
        time_idx: int = rlabels.index("time")
        time_correlations: List[Tuple[str, float]] = list(zip(rlabels, correlation_matrix[time_idx]))
        time_correlations = list(filter(lambda t: -1 <= t[1] <= 1, time_correlations))
        time_correlations.sort(key=lambda t: t[1], reverse=True)
        width: int = max(map(lambda t: len(t[0]), time_correlations))
        for correlation_item in time_correlations:
            print(f"{correlation_item[0]+':': <{width+2}}{correlation_item[1]: .3f}")

    # Generate plots if requested
    if plot_output or interactive:
        # Set up plotting backend
        if not interactive:
            matplotlib.use('Agg')  # Non-interactive backend

        # Create correlation heatmap
        plt.figure(figsize=(12, 10))
        plt.imshow(correlation_matrix, cmap='coolwarm', vmin=-1, vmax=1)
        plt.colorbar()
        plt.xticks(range(len(rlabels)), rlabels, rotation=90)
        plt.yticks(range(len(rlabels)), rlabels)
        plt.title('Correlation Matrix')

        # Save or show the plo
        if plot_output:
            with PdfPages(plot_output) as pdf:
                pdf.savefig()
                plt.close()

                # Create scatter plots for top correlations with time
                if "time" in rlabels:
                    time_idx = rlabels.index("time")
                    time_data: np.ndarray = numeric_data_array[:, time_idx]

                    # Get top 5 correlations with time
                    top_correlations: List[Tuple[int, float]] = sorted([(idx, corr_val) for idx, corr_val in enumerate(correlation_matrix[time_idx])
                                       if idx != time_idx and -1 <= corr_val <= 1],
                                      key=lambda x: abs(x[1]), reverse=True)[:5]

                    for idx, corr_val in top_correlations:
                        plt.figure(figsize=(8, 6))
                        plt.scatter(numeric_data_array[:, idx], time_data)
                        plt.xscale('log')
                        plt.yscale('log')
                        plt.xlabel(rlabels[idx])
                        plt.ylabel('time')
                        plt.title(f'Correlation: {corr_val:.3f}')
                        pdf.savefig()
                        plt.close()

            print(f"Plots saved to {plot_output}")

        if interactive:
            plt.show()

def run_compare_many(args: argparse.Namespace) -> None:
    """Run the comparison of many files against a benchmark."""
    benchmark_path = args.benchmark
    runs_dir = args.dir

    # Read benchmark data
    _, benchmark_data, benchmark_indices = read_and_filter_file(benchmark_path)
    benchmark = extract_basic_data(benchmark_data, benchmark_indices)

    # Get all iteration directories
    runs_dir_path = Path(runs_dir)
    files: List[int] = [int(f.name) for f in runs_dir_path.iterdir() if f.is_dir() and f.name.isdigit()]
    files.sort()

    results: List[Tuple[float, float, int, Optional[int]]] = []
    print(Path(benchmark_path).stem)

    # Process each iteration
    for iteration in files:
        file_path = Path(runs_dir) / str(iteration) / Path(benchmark_path).name
        if not file_path.is_file():
            print(f"Warning: File not found: {file_path}")
            continue

        _, file_data, file_indices = read_and_filter_file(str(file_path))
        file_extracted = extract_basic_data(file_data, file_indices)

        result = compute_stats(benchmark, file_extracted)
        (iteration_runtime, iteration_qi, iteration_regressions, iteration_swaps) = result

        results.append(result)
        print(f"{iteration}: {iteration_runtime:2.3f}% runtime change, {iteration_qi:2.3f}% qi change, {iteration_regressions} stopped working, {iteration_swaps or 'N/A'} swaps")

    # Calculate statistics
    if results:
        # Transpose results using zip and convert each inner sequence to a lis
        transposed_results: List[List[Any]] = [list(row) for row in zip(*results)]

        # Filter out None values for swaps
        valid_swaps = [s for s in transposed_results[3] if s is not None]

        print(f"Avg: {fmean(transposed_results[0]):2.3f}% runtime change, {fmean(transposed_results[1]):2.3f}% qi change, {fmean(transposed_results[2]):2.3f} stopped working, {fmean(valid_swaps) if valid_swaps else 'N/A'} swaps")
        print(f"StDev: {stdev(transposed_results[0]):2.3f} runtime change, {stdev(transposed_results[1]):2.3f} qi change, {stdev(transposed_results[2]):2.3f} stopped working, {stdev(valid_swaps) if valid_swaps else 'N/A'} swaps")
    else:
        print("No results to analyze.")

def run_analysis(args: argparse.Namespace) -> None:
    """Run the analysis tool."""
    file_path = args.file

    # Read and filter data
    header, data, indices = read_and_filter_file(file_path)

    # Add qi_concentration
    qi_idx: int = indices.get("qi", -1)
    qi_top_idx: int = indices.get("qi_top", -1)
    qi_dummys_idx: int = indices.get("qi_dummys", -1)
    qi_dummy_top_idx: int = indices.get("qi_dummy_top", -1)
    qi_top_names_idx: int = indices.get("qi_top_names", -1)

    # Add concentration columns
    header = header + ["qi_concentration", "qi_dummy_concentration"]

    # Calculate concentrations
    for row in data:
        qi_val: int = int(row[qi_idx]) if qi_idx >= 0 else 0
        qi_top_val: int = int(row[qi_top_idx]) if qi_top_idx >= 0 else 0
        qi_dummys_val: int = int(row[qi_dummys_idx]) if qi_dummys_idx >= 0 else 0
        qi_dummy_top_val: int = int(row[qi_dummy_top_idx]) if qi_dummy_top_idx >= 0 else 0

        # Compute QI concentration
        qi_conc: float = 1.0 if qi_val == 0 else qi_top_val / qi_val
        qi_dummy_conc: float = 1.0 if qi_dummys_val == 0 else qi_dummy_top_val / qi_dummys_val

        row.append(str(qi_conc))
        row.append(str(qi_dummy_conc))

    # Analyze QI stats
    if qi_top_names_idx >= 0:
        qi_stats: List[str] = [row[qi_top_names_idx] for row in data]
        print("=== QUANTIFIER INSTANTIATION STATISTICS ===")
        common: List[Tuple[str, int]] = analyze_qi(qi_stats, args.qi_count)

        if not common:
            print("No QI statistics found")
        else:
            width: int = max(len(name) for name, _ in common)
            for name, count in common:
                print(f"{name+':': <{width+2}}{count: d}")

    # Analyze correlations
    analyze_correlations(header, data, indices, args.plot, args.interactive)



def run_compare(args: argparse.Namespace) -> None:
    """Run the comparison tool."""
    base_a = args.a
    base_b = args.b

    # Find projects from CSV files in base_a
    projects: List[str] = []
    base_a_path = Path(base_a)
    if base_a_path.is_dir():
        for file in base_a_path.iterdir():
            if file.suffix == ".csv":
                project_name = file.stem
                projects.append(project_name)

    if not projects:
        print(f"No CSV files found in {base_a}")
        return

    projects.sort()
    print(f"Found {len(projects)} projects: {', '.join(projects)}")

    for project in projects:
        file_a = Path(base_a) / f"{project}.csv"
        file_b = Path(base_b) / f"{project}.csv"

        if not (file_a.is_file() and file_b.is_file()):
            print(f"Skipping {project} - files not found")
            continue

        print(f"Comparing {project}...")

        # Read and process files
        _, a_data, a_indices = read_and_filter_file(str(file_a))
        _, b_data, b_indices = read_and_filter_file(str(file_b))

        a_processed: List[Tuple[str, float]] = [(row[0], float(row[a_indices["total_time"]])) for row in a_data]
        b_processed: List[Tuple[str, float]] = [(row[0], float(row[b_indices["total_time"]])) for row in b_data]

        a_processed.sort(key=lambda e: e[0])
        b_processed.sort(key=lambda e: e[0])

        # Compare files
        matched: List[Tuple[str, Tuple[float, float]]] = []
        regressions: int = 0
        new: int = 0

        base_a_idx: int = 0
        base_b_idx: int = 0

        while base_a_idx < len(a_processed) or base_b_idx < len(b_processed):
            if base_a_idx >= len(a_processed):
                new += len(b_processed) - base_b_idx
                break
            elif base_b_idx >= len(b_processed):
                regressions += len(a_processed) - base_a_idx
                break
            elif a_processed[base_a_idx][0] < b_processed[base_b_idx][0]:
                regressions += 1
                base_a_idx += 1
            elif a_processed[base_a_idx][0] > b_processed[base_b_idx][0]:
                new += 1
                base_b_idx += 1
            else:
                matched.append((a_processed[base_a_idx][0], (a_processed[base_a_idx][1], b_processed[base_b_idx][1])))
                base_a_idx += 1
                base_b_idx += 1

        # Calculate statistics
        a_sum: float = sum(item[1][0] for item in matched) if matched else 0
        b_sum: float = sum(item[1][1] for item in matched) if matched else 0

        runtime_change: float = (b_sum - a_sum) / a_sum * 100 if a_sum > 0 else 0

        faster: int = 0
        slower: int = 0
        same: int = 0
        faster_sum: float = 0.0
        slower_sum: float = 0.0

        for _, times in matched:
            a_time, b_time = times
            if a_time == b_time or (a_time > 0 and abs((b_time - a_time) / a_time) < 0.15):
                same += 1
            elif a_time < b_time:
                slower_sum += a_time
                slower += 1
            else:
                faster_sum += a_time
                faster += 1

        # Print results
        total_queries = len(matched) + regressions + new
        print(f"Analyzed {total_queries} queries. Of those, {len(matched)} lined up and {regressions} stopped working, while {new} started working.")
        print(f"The overall runtime {'improved' if runtime_change <= 0 else 'worsened'} by {abs(runtime_change):.2f} %.")

        if matched:
            print(f"Of the matching queries {faster} ({faster / len(matched) * 100:.2f} %, {faster_sum / a_sum * 100:.2f} % runtime share) significantly improved, {slower} ({slower / len(matched) * 100:.2f} %, {slower_sum / a_sum * 100:.2f} % runtime share) experienced a marked slowdown, and {same} ({same / len(matched) * 100:.2f} %) stayed roughly the same.")

def main() -> None:
    """Main entry point for the unified CLI."""
    parser = argparse.ArgumentParser(
        description="Unified CLI for Dafny analysis tools",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )

    subparsers = parser.add_subparsers(dest="command", help="Command to run")

    # Analysis command
    analysis_parser = subparsers.add_parser("analyze", help="Analyze a single file")
    analysis_parser.add_argument("file", help="Path to CSV file to analyze")
    analysis_parser.add_argument("--qi-count", type=int, default=100,
                                help="Number of top QI entries to display (default: 100)")
    analysis_parser.add_argument("--plot", help="Save plots to specified PDF file")
    analysis_parser.add_argument("--interactive", action="store_true",
                                help="Show interactive plots")

    # Compare command
    compare_parser = subparsers.add_parser("compare", help="Compare two sets of files")
    compare_parser.add_argument("--a", required=True,
                               help="Base directory for first set of files")
    compare_parser.add_argument("--b", required=True,
                               help="Base directory for second set of files")

    # Compare many command
    compare_many_parser = subparsers.add_parser("compare-many", help="Compare many files against a benchmark")
    compare_many_parser.add_argument("--benchmark", required=True,
                                    help="Path to benchmark CSV file")
    compare_many_parser.add_argument("--dir", required=True,
                                    help="Directory containing results")

    args = parser.parse_args()

    if args.command == "compare-many":
        run_compare_many(args)
    elif args.command == "analyze":
        run_analysis(args)
    elif args.command == "compare":
        run_compare(args)
    else:
        parser.print_help()

if __name__ == "__main__":
    main()
