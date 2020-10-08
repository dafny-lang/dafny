namespace DafnyTests {
  public class ProcessResult {

    public int ExitCode;
    public string StandardOutput;
    public string StandardError;

    public ProcessResult(int exitCode, string standardOutput, string standardError) {
      ExitCode = exitCode;
      StandardOutput = standardOutput;
      StandardError = standardError;
    }
  }
}