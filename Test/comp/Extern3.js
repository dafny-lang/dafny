let Library = (function() {
  let $module = {};

  $module.LibClass = class LibClass {
    // static method CallMeInt(x: int) returns (y: int, z: int)
    static CallMeInt(x) {
      let y = x.plus(new BigNumber(1));
      let z = y.plus(y);
      return [y, z];
    }
    // static method CallMeNative(x: MyInt, b: bool) returns (y: MyInt)
    static CallMeNative(x, b) {
      let y = b ? x + 1 : x - 1;
      return y;
    }
  };
  
  $module.Mixed = class Mixed {
    // static method P()
    static P() {
      process.stdout.write("Mixed.P\n");
    }
  }
  $module.AllExtern = class AllExtern {
    static P() {
      process.stdout.write("AllExtern.P\n");
    }
  };
  
  return $module;
})();
