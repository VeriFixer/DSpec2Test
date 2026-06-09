method {:testEntry} TriangularPrismVolume(base: int, height: int, length: int) returns (volume: int)
    requires base > 0
    requires height > 0
    requires length > 0
    ensures volume == (base * height * length) / 2
{
    volume := (base * height * length) / 2;
}

method {:test} Test9() {
expect 11 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1663 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(11, 10, 1663);
expect r0 == 11 * 10 * 1663 / 2;
}

// REPEAT 10 - TIME: 8.8751417 s
