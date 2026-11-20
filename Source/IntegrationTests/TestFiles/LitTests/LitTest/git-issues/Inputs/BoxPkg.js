// An ordinary extern JavaScript class: no equals method, so generic
// comparison used to crash on it. Dafny models the class with identity
// equality, which the runtime must fall back to.
let BoxPkg = (function() {
  let $module = {};

  $module.Box = class Box {
    constructor () {
    }
  };

  return $module;
})();
