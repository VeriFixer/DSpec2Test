method {:testEntry} SquarePyramidSurfaceArea(baseEdge: int, height: int) returns (area: int)
    requires baseEdge > 0
    requires height > 0
    ensures area == baseEdge * baseEdge + 2 * baseEdge * height
{
    area := baseEdge * baseEdge + 2 * baseEdge * height;
}

method {:test} Test16() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7728 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(108, 7728);
expect r0 == 108 * 108 + 2 * 108 * 7728;
}

// REPEAT 9 - TIME: 12.19022 s
