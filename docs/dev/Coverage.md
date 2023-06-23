

# Viewing Test coverage results

Test coverage data is generated as part of each CI test run, in the "Build and Test" workflow

- Open the [Actions page for this workflow](https://github.com/dafny-lang/dafny/actions/workflows/msbuild.yml)
- Click on a relevant run
- At the bottom of the page (you will likely need to scroll down), in the Artifacts section, click on "test-coverage-results" to download the detailed coverage results.
   - Open (in a browser) the file 'coverage-html/index.html' within the dowloaded folder for an entree to the color-coded source code and data showing coverage numbers
- Also, opening the 'test-coverage-analysis' job at the end of the workflow graph
  shows two job steps that report the summary coverage numbers:
   - "Code-coverage report (Non-LSP)"
   - "Code coverage report (LSP)"

