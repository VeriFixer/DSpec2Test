method {:testEntry} MedianLength(a: int, b: int) returns (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
{
    median := (a + b) / 2;
}

method {:test} Test11() {
expect 2480 > 0 && 204 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2480, 204);
expect r0 == (2480 + 204) / 2;
}

// REPEAT 4 - TIME: 8.4625058 s
