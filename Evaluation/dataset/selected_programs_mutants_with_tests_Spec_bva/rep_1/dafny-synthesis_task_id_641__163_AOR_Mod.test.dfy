// dafny-synthesis_task_id_641.dfy

method {:testEntry} NthNonagonalNumber(n: int) returns (number: int)
  requires n >= 0
  ensures number == n * (7 * n - 5) / 2
{
  number := n * (7 * n - 5) % 2;
}

method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(0);
expect r0 == 0 * (7 * 0 - 5) / 2;
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(100);
expect r0 == 100 * (7 * 100 - 5) / 2;
}

// REPEAT 1 - TIME: 35.1169933 s
