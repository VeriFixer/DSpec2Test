// dafny-synthesis_task_id_268.dfy

method {:testEntry} StarNumber(n: int) returns (star: int)
  requires n >= 0
  ensures star == 6 * n * (n - 1) + 1
{
  star := 6 * n * (n - 1) * 1;
}

method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(0);
expect r0 == 6 * 0 * (0 - 1) + 1;
}

// REPEAT 1 - TIME: 2.8221268 s
