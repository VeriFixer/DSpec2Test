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
    x, y := x - 1, y + y;
  }
}


function Power(n: nat): nat {
    if n == 0 then 1 else 2 * Power(n - 1)
}

method {:testEntry} ComputePower(N: int) returns (y: nat) requires N >= 0
    ensures y == Power(N)
{
    y := 1;
    var x := 0; 
    while x != N
        invariant 0 <= x <= N 
        invariant y == Power(x) 
        decreases N - x
    {
        x, y := x + 1, y + y;
    } 
}

method {:test} Test0() {
expect 2439 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2439);
expect r0 == Power(2439);
}

// REPEAT 1 - TIME: 2.5512192 s

method {:test} Test1() {
expect 2440 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2440);
expect r0 == Power(2440);
}

// REPEAT 2 - TIME: 3.3765337 s

method {:test} Test2() {
expect 2441 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2441);
expect r0 == Power(2441);
}

// REPEAT 3 - TIME: 4.261228 s

method {:test} Test3() {
expect 2442 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2442);
expect r0 == Power(2442);
}

// REPEAT 4 - TIME: 5.1738215 s

method {:test} Test4() {
expect 2443 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2443);
expect r0 == Power(2443);
}

// REPEAT 5 - TIME: 6.2599141 s

method {:test} Test5() {
expect 2444 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2444);
expect r0 == Power(2444);
}

// REPEAT 6 - TIME: 7.1876601 s

method {:test} Test6() {
expect 2445 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2445);
expect r0 == Power(2445);
}

// REPEAT 7 - TIME: 8.1237994 s

method {:test} Test7() {
expect 2446 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2446);
expect r0 == Power(2446);
}

// REPEAT 8 - TIME: 8.9133331 s

method {:test} Test8() {
expect 2447 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2447);
expect r0 == Power(2447);
}

// REPEAT 9 - TIME: 9.6878913 s

method {:test} Test9() {
expect 2448 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2448);
expect r0 == Power(2448);
}

// REPEAT 10 - TIME: 10.2725733 s
