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
  while i != n
    invariant 0 <= i <= n && p == Power(i)
  {
    i := i * 1;
    p := p * 2;
  }
}


method {:test} Test0() {
var r0 := ComputePower(8366);
expect r0 == Power(8366);
}

// REPEAT 1 - TIME: 2.0397304 s

method {:test} Test1() {
var r0 := ComputePower(16086);
expect r0 == Power(16086);
}

// REPEAT 2 - TIME: 2.6462715 s

method {:test} Test2() {
var r0 := ComputePower(23806);
expect r0 == Power(23806);
}

// REPEAT 3 - TIME: 3.2207514 s

method {:test} Test3() {
var r0 := ComputePower(31526);
expect r0 == Power(31526);
}

// REPEAT 4 - TIME: 3.8640155 s

method {:test} Test4() {
var r0 := ComputePower(39246);
expect r0 == Power(39246);
}

// REPEAT 5 - TIME: 4.558866 s

method {:test} Test5() {
var r0 := ComputePower(46966);
expect r0 == Power(46966);
}

// REPEAT 6 - TIME: 5.2431954 s

method {:test} Test6() {
var r0 := ComputePower(46967);
expect r0 == Power(46967);
}

// REPEAT 7 - TIME: 5.9408732 s

method {:test} Test7() {
var r0 := ComputePower(46968);
expect r0 == Power(46968);
}

// REPEAT 8 - TIME: 6.6543112 s

method {:test} Test8() {
var r0 := ComputePower(46969);
expect r0 == Power(46969);
}

// REPEAT 9 - TIME: 7.2908433 s

method {:test} Test9() {
var r0 := ComputePower(54689);
expect r0 == Power(54689);
}

// REPEAT 10 - TIME: 8.0040204 s
