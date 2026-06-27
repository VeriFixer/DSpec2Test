// Dafny_Verify_tmp_tmphq7j0row_Generated_Code_ComputePower.dfy

function Power(n: nat): nat
{
  if n == 0 then
    1
  else
    2 * Power(n - 1)
}

method {:testEntry} ComputePower(n: nat) returns (p: nat)
  ensures p == Power(n)
{
  p := 1;
  var i := 0;
  while false
    invariant 0 <= i <= n && p == Power(i)
  {
    i := i + 1;
    p := p * 2;
  }
}


method {:test} Test0() {
var r0 := ComputePower(8366);
expect r0 == Power(8366);
}

// REPEAT 1 - TIME: 2.1991984 s

method {:test} Test1() {
var r0 := ComputePower(16086);
expect r0 == Power(16086);
}

// REPEAT 2 - TIME: 2.9954797 s

method {:test} Test2() {
var r0 := ComputePower(23806);
expect r0 == Power(23806);
}

// REPEAT 3 - TIME: 3.7671526 s

method {:test} Test3() {
var r0 := ComputePower(31526);
expect r0 == Power(31526);
}

// REPEAT 4 - TIME: 4.4278838 s

method {:test} Test4() {
var r0 := ComputePower(39246);
expect r0 == Power(39246);
}

// REPEAT 5 - TIME: 5.2130345 s

method {:test} Test5() {
var r0 := ComputePower(46966);
expect r0 == Power(46966);
}

// REPEAT 6 - TIME: 6.0348139 s

method {:test} Test6() {
var r0 := ComputePower(46967);
expect r0 == Power(46967);
}

// REPEAT 7 - TIME: 6.6819909 s

method {:test} Test7() {
var r0 := ComputePower(46968);
expect r0 == Power(46968);
}

// REPEAT 8 - TIME: 7.309627 s

method {:test} Test8() {
var r0 := ComputePower(46969);
expect r0 == Power(46969);
}

// REPEAT 9 - TIME: 7.9446441 s

method {:test} Test9() {
var r0 := ComputePower(46970);
expect r0 == Power(46970);
}

// REPEAT 10 - TIME: 8.5736817 s
