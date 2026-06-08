method {:testEntry} ParabolaDirectrix(a: real, h: real, k: real) returns (directrix: real)
    requires a != 0.0
    ensures directrix == k - 1.0 / (4.0 * a)
{
    directrix := k - 1.0 / (4.0 * a);
}

method {:test} Test1() {
expect 9.0/8.0 != 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ParabolaDirectrix(9.0/8.0, 2.0, 9.0/8.0);
expect r0 == 9.0/8.0 - 1.0 / (4.0 * 9.0/8.0);
}

// REPEAT 2 - TIME: 4.3087261 s
