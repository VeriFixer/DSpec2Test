// dafny-synthesis_task_id_430.dfy

method {:testEntry} ParabolaDirectrix(a: real, h: real, k: real)
    returns (directrix: real)
  requires a != 0.0
  ensures directrix == k - 1.0 / (4.0 * a)
{
  directrix := k - 1.0 / (4.0 + a);
}

method {:test} Test0() {
expect 1.0 != 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ParabolaDirectrix(1.0, 0.0, 1.0);
expect r0 == 1.0 - 1.0 / (4.0 * 1.0);
}

// REPEAT 1 - TIME: 2.4392207 s
