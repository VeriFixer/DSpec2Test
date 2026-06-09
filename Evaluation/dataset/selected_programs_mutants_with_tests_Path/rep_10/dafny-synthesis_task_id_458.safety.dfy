method {:testEntry} RectangleArea(length: int, width: int) returns (area: int)
    requires length > 0
    requires width > 0
    ensures area == length * width
{
    area := length * width;
}

method {:test} Test9() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(10, 10);
expect r0 == 10 * 10;
}

// REPEAT 10 - TIME: 6.5874417 s
