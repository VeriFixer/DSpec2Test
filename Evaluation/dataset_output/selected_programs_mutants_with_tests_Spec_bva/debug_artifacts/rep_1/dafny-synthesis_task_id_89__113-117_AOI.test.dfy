// dafny-synthesis_task_id_89.dfy

method {:testEntry} ClosestSmaller(n: int) returns (m: int)
  requires n > 0
  ensures m + 1 == n
{
  m := -(n - 1);
}

method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(1);
expect r0 + 1 == 1;
}
method {:test} Test2() {
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(100);
expect r0 + 1 == 100;
}
method {:test} Test4() {
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(101);
expect r0 + 1 == 101;
}

// REPEAT 1 - TIME: 5.3320159 s
