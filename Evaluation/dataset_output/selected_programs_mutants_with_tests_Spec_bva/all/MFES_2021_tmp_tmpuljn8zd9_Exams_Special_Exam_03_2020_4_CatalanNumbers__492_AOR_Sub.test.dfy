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
  while i < n
    invariant res == C(i) && 0 <= i <= n
    decreases n - i
  {
    ghost var v0 := n - i;
    assert res == C(i) && 0 <= i <= n && i < n && n - i == v0;
    i := i - 1;
    res := (4 * i - 2) * res / (i + 1);
    assert res == C(i) && 0 <= i <= n && 0 <= n - i < v0;
  }
  assert res == C(i) && 0 <= i <= n && i >= n;
}


method {:test} Test0() {
var r0 := calcC(2);
expect r0 == C(2);
}
method {:test} Test1() {
var r0 := calcC(100);
expect r0 == C(100);
}

// REPEAT 1 - TIME: 6.3388627 s

method {:test} Test6() {
var r0 := calcC(101);
expect r0 == C(101);
}

// REPEAT 2 - TIME: 7.5014663 s

method {:test} Test7() {
var r0 := calcC(102);
expect r0 == C(102);
}

// REPEAT 3 - TIME: 8.4463864 s

method {:test} Test8() {
var r0 := calcC(103);
expect r0 == C(103);
}

// REPEAT 4 - TIME: 9.273176 s

method {:test} Test9() {
var r0 := calcC(104);
expect r0 == C(104);
}

// REPEAT 5 - TIME: 10.3211521 s

method {:test} Test10() {
var r0 := calcC(105);
expect r0 == C(105);
}

// REPEAT 6 - TIME: 11.0708142 s

method {:test} Test11() {
var r0 := calcC(106);
expect r0 == C(106);
}

// REPEAT 7 - TIME: 11.8601506 s

method {:test} Test12() {
var r0 := calcC(107);
expect r0 == C(107);
}

// REPEAT 8 - TIME: 12.5841468 s

method {:test} Test13() {
var r0 := calcC(108);
expect r0 == C(108);
}

// REPEAT 9 - TIME: 13.1933213 s

method {:test} Test14() {
var r0 := calcC(109);
expect r0 == C(109);
}

// REPEAT 10 - TIME: 13.796639 s
