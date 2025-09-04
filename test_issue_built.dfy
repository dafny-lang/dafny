const SomeMaps := {map["a" := "b"]}
const OhNo := set x <- (set m <- SomeMaps :: m) :: x
