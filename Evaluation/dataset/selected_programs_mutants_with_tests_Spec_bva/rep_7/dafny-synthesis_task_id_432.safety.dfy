method {:testEntry} MedianLength(a: int, b: int) returns (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
{
    median := (a + b) / 2;
}

method {:test} Test14() {
expect 2486 > 0 && 210 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2486, 210);
expect r0 == (2486 + 210) / 2;
}

// REPEAT 7 - TIME: 10.475585 s
