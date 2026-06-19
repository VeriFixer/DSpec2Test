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
  while i >= n + 1
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

method {:test} Test9() {
var r0 := expt(7720, 5923);
expect r0 == Expt(7720, 5923);
}

// REPEAT 2 - TIME: 8.0887946 s

method {:test} Test10() {
var r0 := expt(7721, 5924);
expect r0 == Expt(7721, 5924);
}

// REPEAT 3 - TIME: 8.9700851 s

method {:test} Test11() {
var r0 := expt(7722, 5925);
expect r0 == Expt(7722, 5925);
}

// REPEAT 4 - TIME: 9.7897357 s

method {:test} Test12() {
var r0 := expt(7723, 5926);
expect r0 == Expt(7723, 5926);
}

// REPEAT 5 - TIME: 10.5168327 s

method {:test} Test13() {
var r0 := expt(7724, 5927);
expect r0 == Expt(7724, 5927);
}

// REPEAT 6 - TIME: 11.311402 s

method {:test} Test14() {
var r0 := expt(7725, 5928);
expect r0 == Expt(7725, 5928);
}

// REPEAT 7 - TIME: 12.0386747 s

method {:test} Test15() {
var r0 := expt(7726, 5929);
expect r0 == Expt(7726, 5929);
}

// REPEAT 8 - TIME: 12.6136973 s

method {:test} Test16() {
var r0 := expt(7727, 5930);
expect r0 == Expt(7727, 5930);
}

// REPEAT 9 - TIME: 13.2954045 s

method {:test} Test17() {
var r0 := expt(7728, 5931);
expect r0 == Expt(7728, 5931);
}

// REPEAT 10 - TIME: 13.8738404 s
