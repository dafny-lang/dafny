module M {
    export
        provides A, 
                 A.foo, // want to export foo, which refers to x
                 A.x    // to make export set self-consistent, need to export x

    class A {
        var x: int
        function method foo(): int
          reads this
        {
            x
        }
    }
}
