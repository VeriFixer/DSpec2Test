// Dafny_Learning_Experience_tmp_tmpuxvcet_u_week1_7_week5_ComputePower.dfy

function Power(n: nat): nat
{
  if n == 0 then
    1
  else
    2 * Power(n - 1)
}

method {:testEntry} CalcPower(n: nat) returns (p: nat)
  ensures p == 2 * n
{
  p := 2 * n;
}

method {:testEntry} ComputePower(n: nat) returns (p: nat)
  ensures p == Power(n)
{
  p := 1;
  var i := 0;
  while true
    invariant 0 <= i <= n
    invariant p * Power(n - i) == Power(n)
  {
    p := CalcPower(p);
    i := i + 1;
  }
}


method {:test} Test0() {
var r0 := CalcPower(38);
expect r0 == 2 * 38;
}
method {:test} Test1() {
var r0 := ComputePower(2439);
expect r0 == Power(2439);
}

// REPEAT 1 - TIME: 3.1917225 s

method {:test} Test2() {
var r0 := CalcPower(39);
expect r0 == 2 * 39;
}
method {:test} Test3() {
var r0 := ComputePower(2440);
expect r0 == Power(2440);
}

// REPEAT 2 - TIME: 4.6307941 s

method {:test} Test4() {
var r0 := CalcPower(40);
expect r0 == 2 * 40;
}
method {:test} Test5() {
var r0 := ComputePower(2441);
expect r0 == Power(2441);
}

// REPEAT 3 - TIME: 6.02805 s

method {:test} Test6() {
var r0 := CalcPower(41);
expect r0 == 2 * 41;
}
method {:test} Test7() {
var r0 := ComputePower(2442);
expect r0 == Power(2442);
}

// REPEAT 4 - TIME: 7.5032772 s

method {:test} Test8() {
var r0 := CalcPower(42);
expect r0 == 2 * 42;
}
method {:test} Test9() {
var r0 := ComputePower(2443);
expect r0 == Power(2443);
}

// REPEAT 5 - TIME: 9.2253876 s

method {:test} Test10() {
var r0 := CalcPower(43);
expect r0 == 2 * 43;
}
method {:test} Test11() {
var r0 := ComputePower(2444);
expect r0 == Power(2444);
}

// REPEAT 6 - TIME: 10.5392326 s

method {:test} Test12() {
var r0 := CalcPower(44);
expect r0 == 2 * 44;
}
method {:test} Test13() {
var r0 := ComputePower(2445);
expect r0 == Power(2445);
}

// REPEAT 7 - TIME: 11.6642524 s

method {:test} Test14() {
var r0 := CalcPower(45);
expect r0 == 2 * 45;
}
method {:test} Test15() {
var r0 := ComputePower(2446);
expect r0 == Power(2446);
}

// REPEAT 8 - TIME: 12.8744606 s

method {:test} Test16() {
var r0 := CalcPower(46);
expect r0 == 2 * 46;
}
method {:test} Test17() {
var r0 := ComputePower(2447);
expect r0 == Power(2447);
}

// REPEAT 9 - TIME: 13.9717997 s

method {:test} Test18() {
var r0 := CalcPower(47);
expect r0 == 2 * 47;
}
method {:test} Test19() {
var r0 := ComputePower(2448);
expect r0 == Power(2448);
}

// REPEAT 10 - TIME: 14.8856041 s
