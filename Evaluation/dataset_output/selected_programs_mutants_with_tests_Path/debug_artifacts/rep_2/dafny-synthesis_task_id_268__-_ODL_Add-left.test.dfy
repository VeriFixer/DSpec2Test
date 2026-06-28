// dafny-synthesis_task_id_268.dfy

method {:testEntry} StarNumber(n: int) returns (star: int)
  requires n >= 0
  ensures star == 6 * n * (n - 1) + 1
{
  star := 1;
}

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(1);
expect r0 == 6 * 1 * (1 - 1) + 1;
}

// REPEAT 2 - TIME: 2.8048911 s
