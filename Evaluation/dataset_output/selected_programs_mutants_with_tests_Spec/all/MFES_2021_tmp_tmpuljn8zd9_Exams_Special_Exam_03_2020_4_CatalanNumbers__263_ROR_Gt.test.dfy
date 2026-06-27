// MFES_2021_tmp_tmpuljn8zd9_Exams_Special_Exam_03_2020_4_CatalanNumbers.dfy

function C(n: nat): nat
  decreases n
{
  if n == 0 then
    1
  else
    (4 * n - 2) * C(n - 1) / (n + 1)
}

method {:testEntry} calcC(n: nat) returns (res: nat)
  ensures res == C(n)
{
  var i := 0;
  res := 1;
  assert res == C(i) && 0 <= i <= n;
  while i > n
    invariant res == C(i) && 0 <= i <= n
    decreases n - i
  {
    ghost var v0 := n - i;
    assert res == C(i) && 0 <= i <= n && i < n && n - i == v0;
    i := i + 1;
    res := (4 * i - 2) * res / (i + 1);
    assert res == C(i) && 0 <= i <= n && 0 <= n - i < v0;
  }
  assert res == C(i) && 0 <= i <= n && i >= n;
}


method {:test} Test0() {
var r0 := calcC(2);
expect r0 == C(2);
}

// REPEAT 1 - TIME: 3.5760993 s

method {:test} Test1() {
var r0 := calcC(3);
expect r0 == C(3);
}

// REPEAT 2 - TIME: 4.6332867 s

method {:test} Test2() {
var r0 := calcC(4);
expect r0 == C(4);
}

// REPEAT 3 - TIME: 5.6543344 s

method {:test} Test3() {
var r0 := calcC(5);
expect r0 == C(5);
}

// REPEAT 4 - TIME: 6.841671 s

method {:test} Test4() {
var r0 := calcC(6);
expect r0 == C(6);
}

// REPEAT 5 - TIME: 7.8655395 s

method {:test} Test5() {
var r0 := calcC(7);
expect r0 == C(7);
}

// REPEAT 6 - TIME: 8.8596139 s

method {:test} Test6() {
var r0 := calcC(8);
expect r0 == C(8);
}

// REPEAT 7 - TIME: 9.7656357 s

method {:test} Test7() {
var r0 := calcC(9);
expect r0 == C(9);
}

// REPEAT 8 - TIME: 10.5586167 s

method {:test} Test8() {
var r0 := calcC(10);
expect r0 == C(10);
}

// REPEAT 9 - TIME: 11.2330047 s

method {:test} Test9() {
var r0 := calcC(11);
expect r0 == C(11);
}

// REPEAT 10 - TIME: 11.9168175 s
