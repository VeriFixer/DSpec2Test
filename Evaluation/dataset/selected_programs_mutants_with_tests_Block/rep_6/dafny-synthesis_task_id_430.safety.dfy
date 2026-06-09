method {:testEntry} ParabolaDirectrix(a: real, h: real, k: real) returns (directrix: real)
    requires a != 0.0
    ensures directrix == k - 1.0 / (4.0 * a)
{
    directrix := k - 1.0 / (4.0 * a);
}

method {:test} Test5() {
expect 6548653600686649.0/4313772784996488.0 != 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ParabolaDirectrix(6548653600686649.0/4313772784996488.0, 7.0, 6548653600686649.0/4313772784996488.0);
expect r0 == 6548653600686649.0/4313772784996488.0 - 1.0 / (4.0 * 6548653600686649.0/4313772784996488.0);
}

// REPEAT 6 - TIME: 5.6163958 s
