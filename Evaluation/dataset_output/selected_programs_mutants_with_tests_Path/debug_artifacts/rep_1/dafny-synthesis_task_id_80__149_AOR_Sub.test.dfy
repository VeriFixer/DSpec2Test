// dafny-synthesis_task_id_80.dfy

method {:testEntry} TetrahedralNumber(n: int) returns (t: int)
  requires n >= 0
  ensures t == n * (n + 1) * (n + 2) / 6
{
  t := (n * (n + 1) - (n + 2)) / 6;
}

method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(0);
expect r0 == 0 * (0 + 1) * (0 + 2) / 6;
}

// REPEAT 1 - TIME: 1.2895026 s
