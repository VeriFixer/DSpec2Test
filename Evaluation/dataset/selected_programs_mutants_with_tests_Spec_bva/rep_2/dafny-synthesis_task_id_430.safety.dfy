method {:testEntry} ParabolaDirectrix(a: real, h: real, k: real) returns (directrix: real)
    requires a != 0.0
    ensures directrix == k - 1.0 / (4.0 * a)
{
    directrix := k - 1.0 / (4.0 * a);
}

method {:test} Test12() {
expect 80001.0/800.0 != 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ParabolaDirectrix(80001.0/800.0, 2.0, 80801.0/800.0);
expect r0 == 80801.0/800.0 - 1.0 / (4.0 * 80001.0/800.0);
}

// REPEAT 2 - TIME: 8.9294344 s
