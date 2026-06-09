method {:testEntry} ParabolaDirectrix(a: real, h: real, k: real) returns (directrix: real)
    requires a != 0.0
    ensures directrix == k - 1.0 / (4.0 * a)
{
    directrix := k - 1.0 / (4.0 * a);
}

method {:test} Test4() {
expect 78560569.0/54910152.0 != 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ParabolaDirectrix(78560569.0/54910152.0, 6.0, 78560569.0/54910152.0);
expect r0 == 78560569.0/54910152.0 - 1.0 / (4.0 * 78560569.0/54910152.0);
}

// REPEAT 5 - TIME: 4.9729163 s
