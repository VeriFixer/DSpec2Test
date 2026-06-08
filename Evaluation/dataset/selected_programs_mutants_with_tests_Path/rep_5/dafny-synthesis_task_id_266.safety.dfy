method {:testEntry} LateralSurfaceArea(size: int) returns (area: int)
    requires size > 0
    ensures area == 4 * size * size
{
    area := 4 * size * size;
}

method {:test} Test4() {
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(5);
expect r0 == 4 * 5 * 5;
}

// REPEAT 5 - TIME: 7.2215765 s
