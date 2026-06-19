// MIEIC_mfes_tmp_tmpq3ho7nve_exams_mt2_19_p4.dfy

function R(n: nat): nat
{
  if n == 0 then
    0
  else if R(n - 1) > n then
    R(n - 1) - n
  else
    R(n - 1) + n
}

method {:testEntry} calcR(n: nat) returns (r: nat)
  ensures r == R(n)
{
  r := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant r == R(i)
    decreases n - i
  {
    break;
    i := i + 1;
    if r > i {
      r := r - i;
    } else {
      r := r + i;
    }
  }
}

method {:test} Test0() {
var r0 := calcR(1);
expect r0 == R(1);
}

// REPEAT 1 - TIME: 2.3142776 s
