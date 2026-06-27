// M2_tmp_tmp2laaavvl_Software Verification_Exercices_Exo4-CountAndReturn.dfy

method {:testEntry} CountToAndReturnN(n: int) returns (r: int)
  requires n >= 0
  ensures r == n
{
  var i := 0;
  while i >= n
    invariant 0 <= i <= n
  {
    i := i + 1;
  }
  r := i;
}

method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(0);
expect r0 == 0;
}

// REPEAT 1 - TIME: 6.7645862 s
