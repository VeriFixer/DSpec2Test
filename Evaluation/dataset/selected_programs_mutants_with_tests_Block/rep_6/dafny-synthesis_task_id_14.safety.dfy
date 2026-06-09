method {:testEntry} TriangularPrismVolume(base: int, height: int, length: int) returns (volume: int)
    requires base > 0
    requires height > 0
    requires length > 0
    ensures volume == (base * height * length) / 2
{
    volume := (base * height * length) / 2;
}

method {:test} Test5() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(7, 6, 6);
expect r0 == 7 * 6 * 6 / 2;
}

// REPEAT 6 - TIME: 5.3016632 s
