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
  while i < n * 1
    invariant 0 < i <= n + 1
    invariant res == Expt(b, i - 1)
  {
    res := res * b;
    i := i + 1;
  }
}

lemma {:induction a} distributive(x: int, a: nat, b: nat)
  ensures Expt(x, a) * Expt(x, b) == Expt(x, a + b)


method {:test} Test0() {
var r0 := expt(7719, 1);
expect r0 == Expt(7719, 1);
}

// REPEAT 1 - TIME: 2.5771492 s

method {:test} Test1() {
var r0 := expt(7720, 2);
expect r0 == Expt(7720, 2);
}

// REPEAT 2 - TIME: 3.5079014 s

method {:test} Test2() {
var r0 := expt(7721, 3);
expect r0 == Expt(7721, 3);
}

// REPEAT 3 - TIME: 4.6615672 s

method {:test} Test3() {
var r0 := expt(7722, 4);
expect r0 == Expt(7722, 4);
}

// REPEAT 4 - TIME: 5.6083237 s

method {:test} Test4() {
var r0 := expt(7723, 5);
expect r0 == Expt(7723, 5);
}

// REPEAT 5 - TIME: 6.338876 s

method {:test} Test5() {
var r0 := expt(7724, 6);
expect r0 == Expt(7724, 6);
}

// REPEAT 6 - TIME: 7.1959222 s

method {:test} Test6() {
var r0 := expt(7725, 7);
expect r0 == Expt(7725, 7);
}

// REPEAT 7 - TIME: 7.8780018 s

method {:test} Test7() {
var r0 := expt(7726, 8);
expect r0 == Expt(7726, 8);
}

// REPEAT 8 - TIME: 8.4952857 s

method {:test} Test8() {
var r0 := expt(7727, 9);
expect r0 == Expt(7727, 9);
}

// REPEAT 9 - TIME: 9.1340425 s

method {:test} Test9() {
var r0 := expt(7728, 10);
expect r0 == Expt(7728, 10);
}

// REPEAT 10 - TIME: 9.7381536 s
