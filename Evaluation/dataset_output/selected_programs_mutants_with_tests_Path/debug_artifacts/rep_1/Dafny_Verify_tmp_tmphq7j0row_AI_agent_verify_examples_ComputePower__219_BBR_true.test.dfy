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
