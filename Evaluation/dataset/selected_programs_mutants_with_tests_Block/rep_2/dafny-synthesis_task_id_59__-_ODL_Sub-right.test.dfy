// dafny-synthesis_task_id_59.dfy

method {:testEntry} NthOctagonalNumber(n: int) returns (octagonalNumber: int)
  requires n >= 0
  ensures octagonalNumber == n * (3 * n - 2)
{
  octagonalNumber := n * (3 * n);
}

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(1);
expect r0 == 1 * (3 * 1 - 2);
}

// REPEAT 2 - TIME: 2.6580225 s
