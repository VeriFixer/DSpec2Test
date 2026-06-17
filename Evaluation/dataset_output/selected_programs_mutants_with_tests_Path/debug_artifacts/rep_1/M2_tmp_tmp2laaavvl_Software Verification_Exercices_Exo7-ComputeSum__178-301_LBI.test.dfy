// M2_tmp_tmp2laaavvl_Software Verification_Exercices_Exo7-ComputeSum.dfy

function Sum(n: nat): nat
{
  if n == 0 then
    0
  else
    n + Sum(n - 1)
}

method {:testEntry} ComputeSum(n: nat) returns (s: nat)
  ensures s == Sum(n)
{
  s := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == Sum(i)
  {
    break;
    s := s + i + 1;
    i := i + 1;
  }
}

method {:test} Test0() {
var r0 := ComputeSum(40);
expect r0 == Sum(40);
}

// REPEAT 1 - TIME: 7.1650796 s
