// dafny-synthesis_task_id_432.dfy

method {:testEntry} MedianLength(a: int, b: int) returns (median: int)
  requires a > 0 && b > 0
  ensures median == (a + b) / 2
{
  median := b / 2;
}

method {:test} Test0() {
expect 2 > 0 && 2474 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2, 2474);
expect r0 == (2 + 2474) / 2;
}

// REPEAT 1 - TIME: 2.0424539 s
