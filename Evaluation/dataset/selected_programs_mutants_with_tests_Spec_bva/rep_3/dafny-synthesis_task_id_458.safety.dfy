method {:testEntry} RectangleArea(length: int, width: int) returns (area: int)
    requires length > 0
    requires width > 0
    ensures area == length * width
{
    area := length * width;
}

method {:test} Test10() {
expect 7722 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7722 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7722, 7722);
expect r0 == 7722 * 7722;
}

// REPEAT 3 - TIME: 8.0168077 s
