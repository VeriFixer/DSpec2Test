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
  while x != N
    invariant 0 <= x <= N
    invariant y == Power(x)
    decreases N - x
  {
    break;
    x, y := x + 1, y + y;
  }
}


method {:test} Test0() {
expect 2439 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2439);
expect r0 == Power(2439);
}

// REPEAT 1 - TIME: 3.419026 s

method {:test} Test1() {
expect 2440 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2440);
expect r0 == Power(2440);
}

// REPEAT 2 - TIME: 4.4352662 s

method {:test} Test2() {
expect 2441 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2441);
expect r0 == Power(2441);
}

// REPEAT 3 - TIME: 5.4928697 s

method {:test} Test3() {
expect 2442 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2442);
expect r0 == Power(2442);
}

// REPEAT 4 - TIME: 6.3051138 s

method {:test} Test4() {
expect 2443 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2443);
expect r0 == Power(2443);
}

// REPEAT 5 - TIME: 7.1486997 s

method {:test} Test5() {
expect 2444 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2444);
expect r0 == Power(2444);
}

// REPEAT 6 - TIME: 8.0284272 s

method {:test} Test6() {
expect 2445 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2445);
expect r0 == Power(2445);
}

// REPEAT 7 - TIME: 8.8176306 s

method {:test} Test7() {
expect 2446 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2446);
expect r0 == Power(2446);
}

// REPEAT 8 - TIME: 9.6384461 s

method {:test} Test8() {
expect 2447 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2447);
expect r0 == Power(2447);
}

// REPEAT 9 - TIME: 10.2699862 s

method {:test} Test9() {
expect 2448 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2448);
expect r0 == Power(2448);
}

// REPEAT 10 - TIME: 10.8591204 s
