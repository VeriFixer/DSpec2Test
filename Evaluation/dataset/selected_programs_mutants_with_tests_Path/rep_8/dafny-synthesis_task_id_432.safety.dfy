method {:testEntry} MedianLength(a: int, b: int) returns (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
{
    median := (a + b) / 2;
}

method {:test} Test7() {
expect 9 > 0 && 2481 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(9, 2481);
expect r0 == (9 + 2481) / 2;
}

// REPEAT 8 - TIME: 11.1832866 s
