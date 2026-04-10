# Statistics module

The `Statistics` module provides formally verified mathematical functions for basic statistics parameters in Dafny.  
It ensures correctness using contracts (`requires`, `ensures`) and supports proof-based reasoning for numerical computations.

## File Descriptions

- **`Statistics.dfy`**  
  This Contains the full implementation of all statistical functions, including Sum, Mean, Variance, StdDev, Range, Mode, and Median.  
  It defines all verification contracts and imports `MergeSortBy` from Dafny’s standard library. It also uses an extern Sqrt function for handling floating-point computations.

- **`Statistics_Test.dfy`**  
  Includes test methods for validating the functionality of each operation using Dafny’s `{ :test }` annotation.  
  These tests serve as verification that works with Dafny’s formal proofs.

- **`ExternalMath.cs`**  
  Provides the external implementation of mathematical operations particularly square root. 


## Function Descriptions

- **Sum**  
  Computes the total of all elements in a numeric sequence.

- **Mean**  
  Calculates the average of all elements by dividing the sum by the number of elements.

- **Variance**  
  Measures the spread of data by calculating the average of squared deviations from the mean.

- **Standard Deviation**  
  Computes the square root of variance to express data dispersion in the same units as the input values.

- **Median**  
  Returns the middle value of a sorted dataset (or the mean of two middle values for even-length sequences).

- **Range**  
  Determines the difference between the maximum and minimum values in a sequence, representing overall data spread.

- **Mode**  
  Identifies the most frequently occurring element in a sequence.  
  Verification ensures that when multiple elements occur with equal highest frequency, the earliest one is selected.



