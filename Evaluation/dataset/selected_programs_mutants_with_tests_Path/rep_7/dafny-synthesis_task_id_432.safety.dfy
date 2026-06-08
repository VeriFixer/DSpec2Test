method {:testEntry} MedianLength(a: int, b: int) returns (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
{
    median := (a + b) / 2;
}

method {:test} Test6() {
expect 8 > 0 && 2480 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(8, 2480);
expect r0 == (8 + 2480) / 2;
}

// REPEAT 7 - TIME: 10.2570054 s
