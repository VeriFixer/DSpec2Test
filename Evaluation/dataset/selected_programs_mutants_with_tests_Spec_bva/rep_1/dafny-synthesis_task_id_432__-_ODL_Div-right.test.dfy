// dafny-synthesis_task_id_432.dfy

method {:testEntry} MedianLength(a: int, b: int) returns (median: int)
  requires a > 0 && b > 0
  ensures median == (a + b) / 2
{
  median := a + b;
}

method {:test} Test0() {
expect 2474 > 0 && 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2474, 2);
expect r0 == (2474 + 2) / 2;
}
method {:test} Test1() {
expect 1 > 0 && 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(1, 1);
expect r0 == (1 + 1) / 2;
}
method {:test} Test2() {
expect 100 > 0 && 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(100, 1);
expect r0 == (100 + 1) / 2;
}
method {:test} Test4() {
expect 1 > 0 && 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(1, 100);
expect r0 == (1 + 100) / 2;
}
method {:test} Test6() {
expect 1 > 0 && 199 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(1, 199);
expect r0 == (1 + 199) / 2;
}

// REPEAT 1 - TIME: 6.5316948 s
