// FIXME Test currently fails on JavaScript

let Library = (function() {
    let $module = {};

    $module.Class = class Class {
        constructor(n) {
            this.n = n;
        }

        static SayHi() {
            process.stdout.write("Hello!\n");
        }

        Get() {
            return this.n;
        }
    }

    return $module;
})();