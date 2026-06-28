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
  while i != n
    invariant 0 <= i <= n
    invariant p * Power(n - i) == Power(n)
  {
    break;
    p := CalcPower(p);
    i := i + 1;
  }
}


method {:test} Test0() {
var r0 := CalcPower(2437);
expect r0 == 2 * 2437;
}
method {:test} Test1() {
var r0 := ComputePower(5922);
expect r0 == Power(5922);
}

// REPEAT 1 - TIME: 11.5723944 s

method {:test} Test2() {
var r0 := CalcPower(2438);
expect r0 == 2 * 2438;
}
method {:test} Test3() {
var r0 := ComputePower(5961);
expect r0 == Power(5961);
}

// REPEAT 2 - TIME: 19.0625545 s

method {:test} Test4() {
var r0 := CalcPower(2439);
expect r0 == 2 * 2439;
}
method {:test} Test5() {
var r0 := ComputePower(6000);
expect r0 == Power(6000);
}

// REPEAT 3 - TIME: 25.810771 s

method {:test} Test6() {
var r0 := CalcPower(2440);
expect r0 == 2 * 2440;
}
method {:test} Test7() {
var r0 := ComputePower(13720);
expect r0 == Power(13720);
}

// REPEAT 4 - TIME: 32.924239 s

method {:test} Test8() {
var r0 := CalcPower(2441);
expect r0 == 2 * 2441;
}
method {:test} Test9() {
var r0 := ComputePower(13759);
expect r0 == Power(13759);
}

// REPEAT 5 - TIME: 40.4035252 s

method {:test} Test10() {
var r0 := CalcPower(2442);
expect r0 == 2 * 2442;
}
method {:test} Test11() {
var r0 := ComputePower(13798);
expect r0 == Power(13798);
}

// REPEAT 6 - TIME: 48.5552508 s

method {:test} Test12() {
var r0 := CalcPower(2443);
expect r0 == 2 * 2443;
}
method {:test} Test13() {
var r0 := ComputePower(13837);
expect r0 == Power(13837);
}

// REPEAT 7 - TIME: 56.3547809 s

method {:test} Test14() {
var r0 := CalcPower(2444);
expect r0 == 2 * 2444;
}
method {:test} Test15() {
var r0 := ComputePower(15074);
expect r0 == Power(15074);
}

// REPEAT 8 - TIME: 64.2852111 s

method {:test} Test16() {
var r0 := CalcPower(2445);
expect r0 == 2 * 2445;
}
method {:test} Test17() {
var r0 := ComputePower(16311);
expect r0 == Power(16311);
}

// REPEAT 9 - TIME: 73.233862 s

method {:test} Test18() {
var r0 := CalcPower(2446);
expect r0 == 2 * 2446;
}
method {:test} Test19() {
var r0 := ComputePower(24031);
expect r0 == Power(24031);
}

// REPEAT 10 - TIME: 82.175972 s
