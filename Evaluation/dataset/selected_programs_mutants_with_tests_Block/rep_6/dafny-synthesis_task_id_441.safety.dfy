method {:testEntry} CubeSurfaceArea(size: int) returns (area: int)
    requires size > 0
    ensures area == 6 * size * size
{
    area := 6 * size * size;
}

method {:test} Test5() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(6);
expect r0 == 6 * 6 * 6;
}

// REPEAT 6 - TIME: 5.6592817 s
