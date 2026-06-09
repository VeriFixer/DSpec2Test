method {:testEntry} RectangleArea(length: int, width: int) returns (area: int)
    requires length > 0
    requires width > 0
    ensures area == length * width
{
    area := length * width;
}

method {:test} Test17() {
expect 7729 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7729 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7729, 7729);
expect r0 == 7729 * 7729;
}

// REPEAT 10 - TIME: 11.8604152 s
