method {:testEntry} TriangularPrismVolume(base: int, height: int, length: int) returns (volume: int)
    requires base > 0
    requires height > 0
    requires length > 0
    ensures volume == (base * height * length) / 2
{
    volume := (base * height * length) / 2;
}

method {:test} Test18() {
expect 208 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1431 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(208, 108, 1431);
expect r0 == 208 * 108 * 1431 / 2;
}

// REPEAT 9 - TIME: 12.4294405 s
