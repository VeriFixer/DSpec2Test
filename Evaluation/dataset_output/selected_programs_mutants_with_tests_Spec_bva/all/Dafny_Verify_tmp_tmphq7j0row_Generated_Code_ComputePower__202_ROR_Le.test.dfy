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
  while i <= n
    invariant 0 <= i <= n && p == Power(i)
  {
    i := i + 1;
    p := p * 2;
  }
}


method {:test} Test0() {
var r0 := ComputePower(2439);
expect r0 == Power(2439);
}
method {:test} Test1() {
var r0 := ComputePower(100);
expect r0 == Power(100);
}
method {:test} Test3() {
var r0 := ComputePower(7721);
expect r0 == Power(7721);
}

// REPEAT 1 - TIME: 8.5091435 s

method {:test} Test6() {
var r0 := ComputePower(7722);
expect r0 == Power(7722);
}

// REPEAT 2 - TIME: 9.9147761 s

method {:test} Test7() {
var r0 := ComputePower(7723);
expect r0 == Power(7723);
}

// REPEAT 3 - TIME: 10.9152543 s

method {:test} Test8() {
var r0 := ComputePower(7724);
expect r0 == Power(7724);
}

// REPEAT 4 - TIME: 11.9109049 s

method {:test} Test9() {
var r0 := ComputePower(7725);
expect r0 == Power(7725);
}

// REPEAT 5 - TIME: 12.9337164 s

method {:test} Test10() {
var r0 := ComputePower(7726);
expect r0 == Power(7726);
}

// REPEAT 6 - TIME: 14.1856597 s

method {:test} Test11() {
var r0 := ComputePower(7727);
expect r0 == Power(7727);
}

// REPEAT 7 - TIME: 15.2099192 s

method {:test} Test12() {
var r0 := ComputePower(7728);
expect r0 == Power(7728);
}

// REPEAT 8 - TIME: 16.1999014 s

method {:test} Test13() {
var r0 := ComputePower(7729);
expect r0 == Power(7729);
}

// REPEAT 9 - TIME: 17.1018837 s

method {:test} Test14() {
var r0 := ComputePower(7730);
expect r0 == Power(7730);
}

// REPEAT 10 - TIME: 17.9827235 s
