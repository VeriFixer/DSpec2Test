// dafny-programs_tmp_tmpcwodh6qh_src_expt.dfy

function Expt(b: int, n: nat): int
  requires n >= 0
{
  if n == 0 then
    1
  else
    b * Expt(b, n - 1)
}

method {:testEntry} expt(b: int, n: nat) returns (res: int)
  ensures res == Expt(b, n)
{
  var i := 1;
  res := 1;
  while i < n + 1
    invariant 0 < i <= n + 1
    invariant res == Expt(b, i - 1)
  {
    break;
    res := res * b;
    i := i + 1;
  }
}

lemma {:induction a} distributive(x: int, a: nat, b: nat)
  ensures Expt(x, a) * Expt(x, b) == Expt(x, a + b)

method {:test} Test1() {
var r0 := expt(26, 283);
expect r0 == Expt(26, 283);
}

// REPEAT 2 - TIME: 11.6023701 s
