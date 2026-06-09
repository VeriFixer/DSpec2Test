method {:testEntry} TriangularPrismVolume(base: int, height: int, length: int) returns (volume: int)
    requires base > 0
    requires height > 0
    requires length > 0
    ensures volume == (base * height * length) / 2
{
    volume := (base * height * length) / 2;
}

method {:test} Test13() {
expect 203 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1426 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(203, 103, 1426);
expect r0 == 203 * 103 * 1426 / 2;
}

// REPEAT 4 - TIME: 8.8993577 s
