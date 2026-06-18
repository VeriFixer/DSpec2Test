// dafny-synthesis_task_id_89.dfy

method {:testEntry} ClosestSmaller(n: int) returns (m: int)
  requires n > 0
  ensures m + 1 == n
{
  m := -(n - 1);
}

method {:test} Test1() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(2);
expect r0 + 1 == 2;
}

// REPEAT 2 - TIME: 2.9431668 s
