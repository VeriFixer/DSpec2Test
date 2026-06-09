method {:testEntry} SquarePyramidSurfaceArea(baseEdge: int, height: int) returns (area: int)
    requires baseEdge > 0
    requires height > 0
    ensures area == baseEdge * baseEdge + 2 * baseEdge * height
{
    area := baseEdge * baseEdge + 2 * baseEdge * height;
}

method {:test} Test13() {
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7725 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(105, 7725);
expect r0 == 105 * 105 + 2 * 105 * 7725;
}

// REPEAT 6 - TIME: 9.3601897 s
