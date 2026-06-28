// dafny-synthesis_task_id_268.dfy

method {:testEntry} StarNumber(n: int) returns (star: int)
  requires n >= 0
  ensures star == 6 * n * (n - 1) + 1
{
  star := 1;
}

method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(2);
expect r0 == 6 * 2 * (2 - 1) + 1;
}

// REPEAT 3 - TIME: 3.3614826 s
