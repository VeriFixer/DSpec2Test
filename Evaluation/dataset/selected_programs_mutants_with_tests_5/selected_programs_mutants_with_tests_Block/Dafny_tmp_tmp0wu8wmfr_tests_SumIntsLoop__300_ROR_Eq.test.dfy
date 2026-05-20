// Dafny_tmp_tmp0wu8wmfr_tests_SumIntsLoop.dfy

function sumInts(n: int): int
  requires n >= 0
{
  if n == 0 then
    0
  else
    sumInts(n - 1) + n
}

method {:testEntry} SumIntsLoop(n: int) returns (s: int)
  requires n >= 0
  ensures s == sumInts(n)
  ensures s == n * (n + 1) / 2
{
  s := 0;
  var k := 0;
  while k == n
    invariant 0 <= k <= n
    invariant s == sumInts(k)
    invariant s == k * (k + 1) / 2
    decreases n - k
  {
    k := k + 1;
    s := s + k;
  }
}

method {:test} Test0() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumIntsLoop(1);
expect r0 == sumInts(1);
expect r0 == 1 * (1 + 1) / 2;
}
method {:test} Test1() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumIntsLoop(2);
expect r0 == sumInts(2);
expect r0 == 2 * (2 + 1) / 2;
}
method {:test} Test2() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumIntsLoop(3);
expect r0 == sumInts(3);
expect r0 == 3 * (3 + 1) / 2;
}
method {:test} Test3() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumIntsLoop(4);
expect r0 == sumInts(4);
expect r0 == 4 * (4 + 1) / 2;
}
method {:test} Test4() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumIntsLoop(5);
expect r0 == sumInts(5);
expect r0 == 5 * (5 + 1) / 2;
}
