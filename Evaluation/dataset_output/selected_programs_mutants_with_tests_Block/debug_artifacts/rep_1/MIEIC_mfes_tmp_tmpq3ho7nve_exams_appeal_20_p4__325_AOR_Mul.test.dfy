// MIEIC_mfes_tmp_tmpq3ho7nve_exams_appeal_20_p4.dfy

function F(n: nat): nat
{
  if n <= 2 then
    n
  else
    F(n - 1) + F(n - 3)
}

method {:testEntry} calcF(n: nat) returns (res: nat)
  ensures res == F(n)
{
  var a, b, c := 0, 1, 2;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant a == F(i) && b == F(i + 1) && c == F(i + 2)
    decreases n - i
  {
    a, b, c := b, c, a * c;
    i := i + 1;
  }
  res := a;
}

method {:test} Test0() {
var r0 := calcF(0);
expect r0 == F(0);
}

// REPEAT 1 - TIME: 2.3444576 s
