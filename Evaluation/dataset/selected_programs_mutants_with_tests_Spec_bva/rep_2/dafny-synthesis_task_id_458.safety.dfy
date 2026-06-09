method {:testEntry} RectangleArea(length: int, width: int) returns (area: int)
    requires length > 0
    requires width > 0
    ensures area == length * width
{
    area := length * width;
}

method {:test} Test9() {
expect 7721 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7721 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7721, 7721);
expect r0 == 7721 * 7721;
}

// REPEAT 2 - TIME: 6.5296946 s
