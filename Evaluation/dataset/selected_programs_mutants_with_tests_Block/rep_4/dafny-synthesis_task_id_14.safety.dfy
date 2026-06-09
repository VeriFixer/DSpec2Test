method {:testEntry} TriangularPrismVolume(base: int, height: int, length: int) returns (volume: int)
    requires base > 0
    requires height > 0
    requires length > 0
    ensures volume == (base * height * length) / 2
{
    volume := (base * height * length) / 2;
}

method {:test} Test3() {
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(5, 4, 4);
expect r0 == 5 * 4 * 4 / 2;
}

// REPEAT 4 - TIME: 3.8394897 s
