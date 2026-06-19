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
  while i < 1
    invariant 0 < i <= n + 1
    invariant res == Expt(b, i - 1)
  {
    res := res * b;
    i := 1;
  }
}

lemma {:induction a} distributive(x: int, a: nat, b: nat)
  ensures Expt(x, a) * Expt(x, b) == Expt(x, a + b)

method {:test} Test0() {
var r0 := expt(0, 5922);
expect r0 == Expt(0, 5922);
}
method {:test} Test1() {
var r0 := expt(-100, 2439);
expect r0 == Expt(-100, 2439);
}
method {:test} Test2() {
var r0 := expt(100, 2439);
expect r0 == Expt(100, 2439);
}
method {:test} Test3() {
var r0 := expt(0, 100);
expect r0 == Expt(0, 100);
}
method {:test} Test4() {
var r0 := expt(7719, 4681);
expect r0 == Expt(7719, 4681);
}
method {:test} Test5() {
var r0 := expt(1, 2);
expect r0 == Expt(1, 2);
}
method {:test} Test6() {
var r0 := expt(1, 2277);
expect r0 == Expt(1, 2277);
}

// REPEAT 1 - TIME: 7.3140167 s
