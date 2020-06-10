let DafnyProfiling = (function() {
  let $module = {};

  $module.tallies = []

  $module.CodeCoverage = class CodeCoverage {
    static Setup(size) {
      for (let i = 0; i < size; i++) {
        $module.tallies[i] = 0
      }
    }
    static TearDown() {
      for (let i = 0; i < $module.tallies.length; i++) {
        process.stdout.write("" + i + ": " + $module.tallies[i] + "\n");
      }
      $module.tallies = null;
    }
    static Record(id) {
      $module.tallies[id]++
      return true;
    }
  };

  return $module;
})();
