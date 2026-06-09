method {:testEntry} RectangleArea(length: int, width: int) returns (area: int)
    requires length > 0
    requires width > 0
    ensures area == length * width
{
    area := length * width;
}

method {:test} Test15() {
expect 7727 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7727 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7727, 7727);
expect r0 == 7727 * 7727;
}

// REPEAT 8 - TIME: 10.6052131 s
