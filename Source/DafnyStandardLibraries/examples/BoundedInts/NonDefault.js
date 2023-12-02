let Externs = (function() {
    let $module = {};

    $module.NonDefault = class NonDefault {
        static SquareNativeInt(i) {
            return i * i;
        }
    };
    
    return $module;
})();