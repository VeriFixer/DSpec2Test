method {:testEntry} TriangularPrismVolume(base: int, height: int, length: int) returns (volume: int)
    requires base > 0
    requires height > 0
    requires length > 0
    ensures volume == (base * height * length) / 2
{
    volume := (base * height * length) / 2;
}

method {:test} Test4() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(6, 5, 5);
expect r0 == 6 * 5 * 5 / 2;
}

// REPEAT 5 - TIME: 7.2407781 s
