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
  while i <= n
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
var r0 := CalcPower(100);
expect r0 == 2 * 100;
}
method {:test} Test5() {
var r0 := ComputePower(2439);
expect r0 == Power(2439);
}
method {:test} Test6() {
var r0 := ComputePower(100);
expect r0 == Power(100);
}
method {:test} Test8() {
var r0 := ComputePower(7721);
expect r0 == Power(7721);
}

// REPEAT 1 - TIME: 12.8929185 s

method {:test} Test11() {
var r0 := CalcPower(101);
expect r0 == 2 * 101;
}
method {:test} Test12() {
var r0 := ComputePower(7722);
expect r0 == Power(7722);
}

// REPEAT 2 - TIME: 14.4411108 s

method {:test} Test13() {
var r0 := CalcPower(102);
expect r0 == 2 * 102;
}
method {:test} Test14() {
var r0 := ComputePower(7723);
expect r0 == Power(7723);
}

// REPEAT 3 - TIME: 15.8280025 s

method {:test} Test15() {
var r0 := CalcPower(103);
expect r0 == 2 * 103;
}
method {:test} Test16() {
var r0 := ComputePower(7724);
expect r0 == Power(7724);
}

// REPEAT 4 - TIME: 17.2595175 s

method {:test} Test17() {
var r0 := CalcPower(104);
expect r0 == 2 * 104;
}
method {:test} Test18() {
var r0 := ComputePower(7725);
expect r0 == Power(7725);
}

// REPEAT 5 - TIME: 18.6384113 s

method {:test} Test19() {
var r0 := CalcPower(105);
expect r0 == 2 * 105;
}
method {:test} Test20() {
var r0 := ComputePower(7726);
expect r0 == Power(7726);
}

// REPEAT 6 - TIME: 19.8185571 s

method {:test} Test21() {
var r0 := CalcPower(106);
expect r0 == 2 * 106;
}
method {:test} Test22() {
var r0 := ComputePower(7727);
expect r0 == Power(7727);
}

// REPEAT 7 - TIME: 21.3343762 s

method {:test} Test23() {
var r0 := CalcPower(107);
expect r0 == 2 * 107;
}
method {:test} Test24() {
var r0 := ComputePower(7728);
expect r0 == Power(7728);
}

// REPEAT 8 - TIME: 22.5436785 s

method {:test} Test25() {
var r0 := CalcPower(108);
expect r0 == 2 * 108;
}
method {:test} Test26() {
var r0 := ComputePower(7729);
expect r0 == Power(7729);
}

// REPEAT 9 - TIME: 23.9488497 s

method {:test} Test27() {
var r0 := CalcPower(109);
expect r0 == 2 * 109;
}
method {:test} Test28() {
var r0 := ComputePower(7730);
expect r0 == Power(7730);
}

// REPEAT 10 - TIME: 25.262292 s
