method {:testEntry} SquarePyramidSurfaceArea(baseEdge: int, height: int) returns (area: int)
    requires baseEdge > 0
    requires height > 0
    ensures area == baseEdge * baseEdge + 2 * baseEdge * height
{
    area := baseEdge * baseEdge + 2 * baseEdge * height;
}

method {:test} Test12() {
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7724 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(104, 7724);
expect r0 == 104 * 104 + 2 * 104 * 7724;
}

// REPEAT 5 - TIME: 9.4560187 s
