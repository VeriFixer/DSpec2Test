method {:testEntry} TetrahedralNumber(n: int) returns (t: int)
    requires n >= 0
    ensures t == n * (n + 1) * (n + 2) / 6
{
    t := n * (n + 1) * (n + 2) / 6;
}

method {:test} Test5() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(5);
expect r0 == 5 * (5 + 1) * (5 + 2) / 6;
}

// REPEAT 6 - TIME: 8.1877649 s
