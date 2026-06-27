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
  p := 2 + n;
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
    p := CalcPower(p);
    i := i + 1;
  }
}


method {:test} Test0() {
var r0 := CalcPower(2437);
expect r0 == 2 * 2437;
}
method {:test} Test1() {
var r0 := ComputePower(2);
expect r0 == Power(2);
}

// REPEAT 1 - TIME: 2.3568024 s

method {:test} Test2() {
var r0 := CalcPower(2438);
expect r0 == 2 * 2438;
}
method {:test} Test3() {
var r0 := ComputePower(752);
expect r0 == Power(752);
}

// REPEAT 2 - TIME: 3.1738358 s

method {:test} Test4() {
var r0 := CalcPower(2439);
expect r0 == 2 * 2439;
}
method {:test} Test5() {
var r0 := ComputePower(753);
expect r0 == Power(753);
}

// REPEAT 3 - TIME: 4.1873016 s

method {:test} Test6() {
var r0 := CalcPower(2440);
expect r0 == 2 * 2440;
}
method {:test} Test7() {
var r0 := ComputePower(754);
expect r0 == Power(754);
}

// REPEAT 4 - TIME: 5.1068988 s

method {:test} Test8() {
var r0 := CalcPower(2441);
expect r0 == 2 * 2441;
}
method {:test} Test9() {
var r0 := ComputePower(755);
expect r0 == Power(755);
}

// REPEAT 5 - TIME: 6.0224294 s

method {:test} Test10() {
var r0 := CalcPower(2442);
expect r0 == 2 * 2442;
}
method {:test} Test11() {
var r0 := ComputePower(756);
expect r0 == Power(756);
}

// REPEAT 6 - TIME: 7.0133972 s

method {:test} Test12() {
var r0 := CalcPower(2443);
expect r0 == 2 * 2443;
}
method {:test} Test13() {
var r0 := ComputePower(757);
expect r0 == Power(757);
}

// REPEAT 7 - TIME: 7.7848575 s

method {:test} Test14() {
var r0 := CalcPower(2444);
expect r0 == 2 * 2444;
}
method {:test} Test15() {
var r0 := ComputePower(758);
expect r0 == Power(758);
}

// REPEAT 8 - TIME: 8.8870574 s

method {:test} Test16() {
var r0 := CalcPower(2445);
expect r0 == 2 * 2445;
}
method {:test} Test17() {
var r0 := ComputePower(759);
expect r0 == Power(759);
}

// REPEAT 9 - TIME: 9.8948502 s

method {:test} Test18() {
var r0 := CalcPower(2446);
expect r0 == 2 * 2446;
}
method {:test} Test19() {
var r0 := ComputePower(760);
expect r0 == Power(760);
}

// REPEAT 10 - TIME: 10.7181501 s
