method {:testEntry} SquarePyramidSurfaceArea(baseEdge: int, height: int) returns (area: int)
    requires baseEdge > 0
    requires height > 0
    ensures area == baseEdge * baseEdge + 2 * baseEdge * height
{
    area := baseEdge * baseEdge + 2 * baseEdge * height;
}

method {:test} Test17() {
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7729 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(109, 7729);
expect r0 == 109 * 109 + 2 * 109 * 7729;
}

// REPEAT 10 - TIME: 12.0739798 s
