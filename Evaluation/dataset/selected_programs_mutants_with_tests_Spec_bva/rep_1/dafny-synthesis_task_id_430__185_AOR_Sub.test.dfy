// dafny-synthesis_task_id_430.dfy

method {:testEntry} ParabolaDirectrix(a: real, h: real, k: real)
    returns (directrix: real)
  requires a != 0.0
  ensures directrix == k - 1.0 / (4.0 * a)
{
  directrix := k - (1.0 - 4.0 * a);
}

method {:test} Test0() {
expect 1.0 != 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ParabolaDirectrix(1.0, 0.0, 1.0);
expect r0 == 1.0 - 1.0 / (4.0 * 1.0);
}
method {:test} Test1() {
expect -100.0 != 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ParabolaDirectrix(-100.0, 0.0, 0.0);
expect r0 == 0.0 - 1.0 / (4.0 * -100.0);
}
method {:test} Test2() {
expect 100.0 != 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ParabolaDirectrix(100.0, 0.0, 0.0);
expect r0 == 0.0 - 1.0 / (4.0 * 100.0);
}
method {:test} Test3() {
expect 1.0 != 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ParabolaDirectrix(1.0, -100.0, 1.0);
expect r0 == 1.0 - 1.0 / (4.0 * 1.0);
}
method {:test} Test4() {
expect 1.0 != 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ParabolaDirectrix(1.0, 100.0, 1.0);
expect r0 == 1.0 - 1.0 / (4.0 * 1.0);
}
method {:test} Test5() {
expect 1.0 != 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ParabolaDirectrix(1.0, 0.0, -100.0);
expect r0 == -100.0 - 1.0 / (4.0 * 1.0);
}
method {:test} Test6() {
expect 1.0 != 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ParabolaDirectrix(1.0, 0.0, 100.0);
expect r0 == 100.0 - 1.0 / (4.0 * 1.0);
}
method {:test} Test8() {
expect 1.0 != 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ParabolaDirectrix(1.0, 0.0, -99.0);
expect r0 == -99.0 - 1.0 / (4.0 * 1.0);
}
method {:test} Test9() {
expect 1.0 != 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ParabolaDirectrix(1.0, 0.0, 101.0);
expect r0 == 101.0 - 1.0 / (4.0 * 1.0);
}

// REPEAT 1 - TIME: 8.3173057 s
