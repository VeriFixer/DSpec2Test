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
  p := n;
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

// REPEAT 1 - TIME: 2.508482 s

method {:test} Test2() {
var r0 := CalcPower(2438);
expect r0 == 2 * 2438;
}
method {:test} Test3() {
var r0 := ComputePower(5);
expect r0 == Power(5);
}

// REPEAT 2 - TIME: 3.4876322 s

method {:test} Test4() {
var r0 := CalcPower(2439);
expect r0 == 2 * 2439;
}
method {:test} Test5() {
var r0 := ComputePower(6);
expect r0 == Power(6);
}

// REPEAT 3 - TIME: 4.33965 s

method {:test} Test6() {
var r0 := CalcPower(2440);
expect r0 == 2 * 2440;
}
method {:test} Test7() {
var r0 := ComputePower(7);
expect r0 == Power(7);
}

// REPEAT 4 - TIME: 5.4232444 s

method {:test} Test8() {
var r0 := CalcPower(2441);
expect r0 == 2 * 2441;
}
method {:test} Test9() {
var r0 := ComputePower(8);
expect r0 == Power(8);
}

// REPEAT 5 - TIME: 6.5796295 s

method {:test} Test10() {
var r0 := CalcPower(2442);
expect r0 == 2 * 2442;
}
method {:test} Test11() {
var r0 := ComputePower(9);
expect r0 == Power(9);
}

// REPEAT 6 - TIME: 7.5383565 s

method {:test} Test12() {
var r0 := CalcPower(2443);
expect r0 == 2 * 2443;
}
method {:test} Test13() {
var r0 := ComputePower(10);
expect r0 == Power(10);
}

// REPEAT 7 - TIME: 8.381086 s

method {:test} Test14() {
var r0 := CalcPower(2444);
expect r0 == 2 * 2444;
}
method {:test} Test15() {
var r0 := ComputePower(11);
expect r0 == Power(11);
}

// REPEAT 8 - TIME: 9.1885 s

method {:test} Test16() {
var r0 := CalcPower(2445);
expect r0 == 2 * 2445;
}
method {:test} Test17() {
var r0 := ComputePower(12);
expect r0 == Power(12);
}

// REPEAT 9 - TIME: 9.9698815 s

method {:test} Test18() {
var r0 := CalcPower(2446);
expect r0 == 2 * 2446;
}
method {:test} Test19() {
var r0 := ComputePower(13);
expect r0 == Power(13);
}

// REPEAT 10 - TIME: 10.8541973 s
