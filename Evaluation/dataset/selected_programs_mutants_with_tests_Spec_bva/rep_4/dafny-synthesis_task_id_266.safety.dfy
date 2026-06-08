method {:testEntry} LateralSurfaceArea(size: int) returns (area: int)
    requires size > 0
    ensures area == 4 * size * size
{
    area := 4 * size * size;
}

method {:test} Test8() {
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(103);
expect r0 == 4 * 103 * 103;
}

// REPEAT 4 - TIME: 8.3518494 s
