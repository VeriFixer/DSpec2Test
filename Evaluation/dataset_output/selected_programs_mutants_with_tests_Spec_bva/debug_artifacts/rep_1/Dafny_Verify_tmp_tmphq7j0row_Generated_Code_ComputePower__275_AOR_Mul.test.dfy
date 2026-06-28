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
