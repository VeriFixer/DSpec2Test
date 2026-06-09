method {:testEntry} ParabolaDirectrix(a: real, h: real, k: real) returns (directrix: real)
    requires a != 0.0
    ensures directrix == k - 1.0 / (4.0 * a)
{
    directrix := k - 1.0 / (4.0 * a);
}

method {:test} Test3() {
expect 8569.0/6408.0 != 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ParabolaDirectrix(8569.0/6408.0, 5.0, 8569.0/6408.0);
expect r0 == 8569.0/6408.0 - 1.0 / (4.0 * 8569.0/6408.0);
}

// REPEAT 4 - TIME: 2.5820277 s
