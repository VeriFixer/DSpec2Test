method {:testEntry} LateralSurfaceArea(size: int) returns (area: int)
    requires size > 0
    ensures area == 4 * size * size
{
    area := 4 * size * size;
}

method {:test} Test9() {
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(104);
expect r0 == 4 * 104 * 104;
}

// REPEAT 5 - TIME: 9.0248986 s
