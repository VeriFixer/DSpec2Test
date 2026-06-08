method {:testEntry} SquarePyramidSurfaceArea(baseEdge: int, height: int) returns (area: int)
    requires baseEdge > 0
    requires height > 0
    ensures area == baseEdge * baseEdge + 2 * baseEdge * height
{
    area := baseEdge * baseEdge + 2 * baseEdge * height;
}

method {:test} Test8() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(9, 9);
expect r0 == 9 * 9 + 2 * 9 * 9;
}

// REPEAT 9 - TIME: 12.3432467 s
