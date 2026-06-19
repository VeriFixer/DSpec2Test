// Dafny_Verify_tmp_tmphq7j0row_AI_agent_verify_examples_ComputePower.dfy

function Power(n: nat): nat
{
  if n == 0 then
    1
  else
    2 * Power(n - 1)
}

method {:testEntry} ComputePower(N: int) returns (y: nat)
  requires N >= 0
  ensures y == Power(N)
{
  y := 1;
  var x := 0;
  while true
    invariant 0 <= x <= N
    invariant y == Power(x)
    decreases N - x
  {
    x, y := x + 1, y + y;
  }
}


method {:test} Test0() {
expect 1798 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(1798);
expect r0 == Power(1798);
}

// REPEAT 1 - TIME: 8.107842 s

method {:test} Test1() {
expect 1799 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(1799);
expect r0 == Power(1799);
}

// REPEAT 2 - TIME: 13.2781202 s

method {:test} Test2() {
expect 1800 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(1800);
expect r0 == Power(1800);
}

// REPEAT 3 - TIME: 17.6962934 s

method {:test} Test3() {
expect 1801 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(1801);
expect r0 == Power(1801);
}

// REPEAT 4 - TIME: 21.3856657 s

method {:test} Test4() {
expect 1802 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(1802);
expect r0 == Power(1802);
}

// REPEAT 5 - TIME: 25.8978302 s

method {:test} Test5() {
expect 1803 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(1803);
expect r0 == Power(1803);
}

// REPEAT 6 - TIME: 29.9180735 s

method {:test} Test6() {
expect 1804 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(1804);
expect r0 == Power(1804);
}

// REPEAT 7 - TIME: 33.9138954 s

method {:test} Test7() {
expect 1805 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(1805);
expect r0 == Power(1805);
}

// REPEAT 8 - TIME: 38.4853664 s

method {:test} Test8() {
expect 1806 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(1806);
expect r0 == Power(1806);
}

// REPEAT 9 - TIME: 42.3428682 s

method {:test} Test9() {
expect 1807 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(1807);
expect r0 == Power(1807);
}

// REPEAT 10 - TIME: 46.9473246 s
