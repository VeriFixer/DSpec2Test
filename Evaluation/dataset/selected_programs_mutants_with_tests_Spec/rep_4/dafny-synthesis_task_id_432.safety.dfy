method {:testEntry} MedianLength(a: int, b: int) returns (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
{
    median := (a + b) / 2;
}

method {:test} Test3() {
expect 2480 > 0 && 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2480, 8);
expect r0 == (2480 + 8) / 2;
}

// REPEAT 4 - TIME: 5.2130815 s
