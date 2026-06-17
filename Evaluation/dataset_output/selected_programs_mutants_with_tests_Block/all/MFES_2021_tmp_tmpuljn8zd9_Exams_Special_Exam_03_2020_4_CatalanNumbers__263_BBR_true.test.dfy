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
  while true
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


function C(n: nat): nat 
    decreases n
{
    if n == 0 then 1 else (4 * n - 2) * C(n-1) / (n + 1) 
}

method {:testEntry} calcC(n: nat) returns (res: nat)
    ensures res == C(n)
{
    var i := 0;
    res := 1;

  assert res == C(i) && 0 <= i <= n;
    while i < n 
        decreases n - i //a - loop variant
        invariant res == C(i) && 0 <= i <= n //b - loop invariant
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
method {:test} Test1() {
var r0 := calcC(12);
expect r0 == C(12);
}

// REPEAT 1 - TIME: 3.9765093 s

method {:test} Test2() {
var r0 := calcC(13);
expect r0 == C(13);
}

// REPEAT 2 - TIME: 5.5458793 s

method {:test} Test4() {
var r0 := calcC(14);
expect r0 == C(14);
}

// REPEAT 3 - TIME: 6.7772399 s

method {:test} Test6() {
var r0 := calcC(15);
expect r0 == C(15);
}

// REPEAT 4 - TIME: 8.015699 s

method {:test} Test8() {
var r0 := calcC(16);
expect r0 == C(16);
}

// REPEAT 5 - TIME: 9.3863233 s

method {:test} Test10() {
var r0 := calcC(17);
expect r0 == C(17);
}

// REPEAT 6 - TIME: 10.4263858 s

method {:test} Test12() {
var r0 := calcC(18);
expect r0 == C(18);
}

// REPEAT 7 - TIME: 11.4739005 s

method {:test} Test14() {
var r0 := calcC(19);
expect r0 == C(19);
}

// REPEAT 8 - TIME: 12.41118 s

method {:test} Test16() {
var r0 := calcC(20);
expect r0 == C(20);
}

// REPEAT 9 - TIME: 13.5071924 s

method {:test} Test18() {
var r0 := calcC(21);
expect r0 == C(21);
}

// REPEAT 10 - TIME: 14.4667366 s
