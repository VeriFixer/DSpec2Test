function Expt(b: int, n: nat): int
  requires n >= 0
{
  if n == 0 then 1 else b * Expt(b, n - 1)
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
    res := res * b;
    i := i + 1;
  }
}

// source: https://www.dcc.fc.up.pt/~nam/web/resources/vfs20/DafnyQuickReference.pdf
lemma {:induction a} distributive(x: int, a: nat, b: nat) 
  ensures Expt(x, a) * Expt(x, b) == Expt(x, a + b)

method {:test} Test0() {
var r0 := expt(0, 5922);
expect r0 == Expt(0, 5922);
}

// REPEAT 1 - TIME: 3.4880381 s

method {:test} Test1() {
var r0 := expt(1, 5923);
expect r0 == Expt(1, 5923);
}

// REPEAT 2 - TIME: 4.6335264 s

method {:test} Test2() {
var r0 := expt(2, 5924);
expect r0 == Expt(2, 5924);
}

// REPEAT 3 - TIME: 5.6459439 s

method {:test} Test3() {
var r0 := expt(284, 5925);
expect r0 == Expt(284, 5925);
}

// REPEAT 4 - TIME: 6.6240674 s

method {:test} Test4() {
var r0 := expt(285, 5926);
expect r0 == Expt(285, 5926);
}

// REPEAT 5 - TIME: 7.6919722 s

method {:test} Test5() {
var r0 := expt(286, 5927);
expect r0 == Expt(286, 5927);
}

// REPEAT 6 - TIME: 8.6255535 s

method {:test} Test6() {
var r0 := expt(287, 5928);
expect r0 == Expt(287, 5928);
}

// REPEAT 7 - TIME: 9.466481 s

method {:test} Test7() {
var r0 := expt(288, 5929);
expect r0 == Expt(288, 5929);
}

// REPEAT 8 - TIME: 10.3850357 s

method {:test} Test8() {
var r0 := expt(289, 5930);
expect r0 == Expt(289, 5930);
}

// REPEAT 9 - TIME: 11.3947677 s

method {:test} Test9() {
var r0 := expt(290, 5931);
expect r0 == Expt(290, 5931);
}

// REPEAT 10 - TIME: 12.1949154 s
