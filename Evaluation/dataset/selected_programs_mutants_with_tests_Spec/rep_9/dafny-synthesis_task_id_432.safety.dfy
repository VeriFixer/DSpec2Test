method {:testEntry} MedianLength(a: int, b: int) returns (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
{
    median := (a + b) / 2;
}

method {:test} Test8() {
expect 2490 > 0 && 18 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2490, 18);
expect r0 == (2490 + 18) / 2;
}

// REPEAT 9 - TIME: 9.6909365 s
