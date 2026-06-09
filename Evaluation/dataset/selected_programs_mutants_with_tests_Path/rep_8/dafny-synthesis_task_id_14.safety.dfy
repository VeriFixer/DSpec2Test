method {:testEntry} TriangularPrismVolume(base: int, height: int, length: int) returns (volume: int)
    requires base > 0
    requires height > 0
    requires length > 0
    ensures volume == (base * height * length) / 2
{
    volume := (base * height * length) / 2;
}

method {:test} Test7() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5928 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(9, 8, 5928);
expect r0 == 9 * 8 * 5928 / 2;
}

// REPEAT 8 - TIME: 10.1690982 s
