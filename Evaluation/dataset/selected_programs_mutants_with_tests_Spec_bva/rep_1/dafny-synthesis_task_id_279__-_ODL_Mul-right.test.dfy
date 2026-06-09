// dafny-synthesis_task_id_279.dfy

method {:testEntry} NthDecagonalNumber(n: int) returns (decagonal: int)
  requires n >= 0
  ensures decagonal == 4 * n * n - 3 * n
{
  decagonal := 4 - 3;
}

method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(0);
expect r0 == 4 * 0 * 0 - 3 * 0;
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(100);
expect r0 == 4 * 100 * 100 - 3 * 100;
}

// REPEAT 1 - TIME: 4.4356 s
