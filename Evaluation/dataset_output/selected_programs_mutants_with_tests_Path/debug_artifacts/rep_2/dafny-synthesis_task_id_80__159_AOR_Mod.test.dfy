// dafny-synthesis_task_id_80.dfy

method {:testEntry} TetrahedralNumber(n: int) returns (t: int)
  requires n >= 0
  ensures t == n * (n + 1) * (n + 2) / 6
{
  t := n * (n + 1) * (n + 2) % 6;
}

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(1);
expect r0 == 1 * (1 + 1) * (1 + 2) / 6;
}

// REPEAT 2 - TIME: 2.7151212 s
