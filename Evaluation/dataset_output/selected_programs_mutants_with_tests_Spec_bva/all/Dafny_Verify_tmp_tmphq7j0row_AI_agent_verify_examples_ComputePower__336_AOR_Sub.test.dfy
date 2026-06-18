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
method {:test} Test1() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(0);
expect r0 == Power(0);
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(100);
expect r0 == Power(100);
}
method {:test} Test4() {
expect 7721 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(7721);
expect r0 == Power(7721);
}

// REPEAT 1 - TIME: 5.8224082 s

method {:test} Test7() {
expect 7722 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(7722);
expect r0 == Power(7722);
}

// REPEAT 2 - TIME: 6.7938227 s

method {:test} Test8() {
expect 7723 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(7723);
expect r0 == Power(7723);
}

// REPEAT 3 - TIME: 7.7619672 s

method {:test} Test9() {
expect 7724 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(7724);
expect r0 == Power(7724);
}

// REPEAT 4 - TIME: 8.5381332 s

method {:test} Test10() {
expect 7725 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(7725);
expect r0 == Power(7725);
}

// REPEAT 5 - TIME: 9.2204235 s

method {:test} Test11() {
expect 7726 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(7726);
expect r0 == Power(7726);
}

// REPEAT 6 - TIME: 10.1165993 s

method {:test} Test12() {
expect 7727 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(7727);
expect r0 == Power(7727);
}

// REPEAT 7 - TIME: 10.8179173 s

method {:test} Test13() {
expect 7728 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(7728);
expect r0 == Power(7728);
}

// REPEAT 8 - TIME: 11.6309793 s

method {:test} Test14() {
expect 7729 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(7729);
expect r0 == Power(7729);
}

// REPEAT 9 - TIME: 12.3831477 s

method {:test} Test15() {
expect 7730 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(7730);
expect r0 == Power(7730);
}

// REPEAT 10 - TIME: 13.1127801 s
