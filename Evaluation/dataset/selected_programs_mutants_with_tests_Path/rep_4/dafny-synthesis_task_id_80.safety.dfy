method {:testEntry} TetrahedralNumber(n: int) returns (t: int)
    requires n >= 0
    ensures t == n * (n + 1) * (n + 2) / 6
{
    t := n * (n + 1) * (n + 2) / 6;
}

method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(3);
expect r0 == 3 * (3 + 1) * (3 + 2) / 6;
}

// REPEAT 4 - TIME: 6.1986565 s
