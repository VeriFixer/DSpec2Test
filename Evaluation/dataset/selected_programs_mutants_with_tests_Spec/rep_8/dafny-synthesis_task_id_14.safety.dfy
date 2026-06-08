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
expect 1661 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(9, 8, 1661);
expect r0 == 9 * 8 * 1661 / 2;
}

// REPEAT 8 - TIME: 9.4935735 s
