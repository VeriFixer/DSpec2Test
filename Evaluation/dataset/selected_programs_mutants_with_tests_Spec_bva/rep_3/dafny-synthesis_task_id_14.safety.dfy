method {:testEntry} TriangularPrismVolume(base: int, height: int, length: int) returns (volume: int)
    requires base > 0
    requires height > 0
    requires length > 0
    ensures volume == (base * height * length) / 2
{
    volume := (base * height * length) / 2;
}

method {:test} Test12() {
expect 202 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1425 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(202, 102, 1425);
expect r0 == 202 * 102 * 1425 / 2;
}

// REPEAT 3 - TIME: 8.2552164 s
