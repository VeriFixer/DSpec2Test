method {:testEntry} SquarePyramidSurfaceArea(baseEdge: int, height: int) returns (area: int)
    requires baseEdge > 0
    requires height > 0
    ensures area == baseEdge * baseEdge + 2 * baseEdge * height
{
    area := baseEdge * baseEdge + 2 * baseEdge * height;
}

method {:test} Test10() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7722 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(102, 7722);
expect r0 == 102 * 102 + 2 * 102 * 7722;
}

// REPEAT 3 - TIME: 8.0392697 s
