// dafny-synthesis_task_id_435.dfy

method {:testEntry} LastDigit(n: int) returns (d: int)
  requires n >= 0
  ensures 0 <= d < 10
  ensures n % 10 == d
{
  d := n - 10;
}

method {:test} Test0() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LastDigit(8);
expect 0 <= r0 < 10;
expect 8 % 10 == r0;
}
method {:test} Test1() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LastDigit(0);
expect 0 <= r0 < 10;
expect 0 % 10 == r0;
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LastDigit(100);
expect 0 <= r0 < 10;
expect 100 % 10 == r0;
}
method {:test} Test4() {
expect 12360 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LastDigit(12360);
expect 0 <= r0 < 10;
expect 12360 % 10 == r0;
}
method {:test} Test5() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LastDigit(9);
expect 0 <= r0 < 10;
expect 9 % 10 == r0;
}
method {:test} Test6() {
expect 12369 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LastDigit(12369);
expect 0 <= r0 < 10;
expect 12369 % 10 == r0;
}

// REPEAT 1 - TIME: 6.0639101 s
