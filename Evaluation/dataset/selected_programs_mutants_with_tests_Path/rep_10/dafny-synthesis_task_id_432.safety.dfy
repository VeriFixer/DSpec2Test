method {:testEntry} MedianLength(a: int, b: int) returns (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
{
    median := (a + b) / 2;
}

method {:test} Test9() {
expect 11 > 0 && 2483 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(11, 2483);
expect r0 == (11 + 2483) / 2;
}

// REPEAT 10 - TIME: 13.0593589 s
