method {:testEntry} SquarePyramidSurfaceArea(baseEdge: int, height: int) returns (area: int)
    requires baseEdge > 0
    requires height > 0
    ensures area == baseEdge * baseEdge + 2 * baseEdge * height
{
    area := baseEdge * baseEdge + 2 * baseEdge * height;
}

method {:test} Test14() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7726 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(106, 7726);
expect r0 == 106 * 106 + 2 * 106 * 7726;
}

// REPEAT 7 - TIME: 9.984784 s
