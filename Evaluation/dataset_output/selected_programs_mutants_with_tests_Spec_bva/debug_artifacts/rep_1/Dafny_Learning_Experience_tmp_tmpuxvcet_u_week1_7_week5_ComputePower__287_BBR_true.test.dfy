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
