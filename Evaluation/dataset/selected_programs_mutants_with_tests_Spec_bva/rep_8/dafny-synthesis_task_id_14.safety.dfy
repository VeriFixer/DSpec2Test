method {:testEntry} TriangularPrismVolume(base: int, height: int, length: int) returns (volume: int)
    requires base > 0
    requires height > 0
    requires length > 0
    ensures volume == (base * height * length) / 2
{
    volume := (base * height * length) / 2;
}

method {:test} Test17() {
expect 207 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1430 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(207, 107, 1430);
expect r0 == 207 * 107 * 1430 / 2;
}

// REPEAT 8 - TIME: 12.5604797 s
