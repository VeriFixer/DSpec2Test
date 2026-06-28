// dafny-synthesis_task_id_435.dfy

method {:testEntry} LastDigit(n: int) returns (d: int)
  requires n >= 0
  ensures 0 <= d < 10
  ensures n % 10 == d
{
  d := n;
}

method {:test} Test1() {
expect 12370 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LastDigit(12370);
expect 0 <= r0 < 10;
expect 12370 % 10 == r0;
}

// REPEAT 2 - TIME: 3.422015 s
