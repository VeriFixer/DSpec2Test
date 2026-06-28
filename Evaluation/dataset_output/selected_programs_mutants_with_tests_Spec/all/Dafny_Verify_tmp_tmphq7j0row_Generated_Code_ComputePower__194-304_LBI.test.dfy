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
    break;
    i := i + 1;
    p := p * 2;
  }
}


method {:test} Test0() {
var r0 := ComputePower(2439);
expect r0 == Power(2439);
}

// REPEAT 1 - TIME: 2.9863662 s

method {:test} Test1() {
var r0 := ComputePower(2440);
expect r0 == Power(2440);
}

// REPEAT 2 - TIME: 3.8740126 s

method {:test} Test2() {
var r0 := ComputePower(2441);
expect r0 == Power(2441);
}

// REPEAT 3 - TIME: 4.7947952 s

method {:test} Test3() {
var r0 := ComputePower(2442);
expect r0 == Power(2442);
}

// REPEAT 4 - TIME: 5.821236 s

method {:test} Test4() {
var r0 := ComputePower(2443);
expect r0 == Power(2443);
}

// REPEAT 5 - TIME: 6.7737346 s

method {:test} Test5() {
var r0 := ComputePower(2444);
expect r0 == Power(2444);
}

// REPEAT 6 - TIME: 7.6762105 s

method {:test} Test6() {
var r0 := ComputePower(2445);
expect r0 == Power(2445);
}

// REPEAT 7 - TIME: 8.7161718 s

method {:test} Test7() {
var r0 := ComputePower(2446);
expect r0 == Power(2446);
}

// REPEAT 8 - TIME: 9.5875775 s

method {:test} Test8() {
var r0 := ComputePower(2447);
expect r0 == Power(2447);
}

// REPEAT 9 - TIME: 10.3690985 s

method {:test} Test9() {
var r0 := ComputePower(2448);
expect r0 == Power(2448);
}

// REPEAT 10 - TIME: 11.158268 s
