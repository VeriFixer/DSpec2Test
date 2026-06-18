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
    i := i * 1;
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
var r0 := calcC(3);
expect r0 == C(3);
}

// REPEAT 1 - TIME: 33.2096277 s

method {:test} Test2() {
var r0 := calcC(4);
expect r0 == C(4);
}

// REPEAT 2 - TIME: 34.6818551 s

method {:test} Test4() {
var r0 := calcC(43);
expect r0 == C(43);
}
method {:test} Test5() {
var r0 := calcC(5);
expect r0 == C(5);
}

// REPEAT 3 - TIME: 35.816754 s

method {:test} Test6() {
var r0 := calcC(44);
expect r0 == C(44);
}

// REPEAT 4 - TIME: 36.945953 s

method {:test} Test8() {
var r0 := calcC(45);
expect r0 == C(45);
}

// REPEAT 5 - TIME: 37.8233814 s

method {:test} Test10() {
var r0 := calcC(46);
expect r0 == C(46);
}

// REPEAT 6 - TIME: 38.7901647 s

method {:test} Test12() {
var r0 := calcC(47);
expect r0 == C(47);
}

// REPEAT 7 - TIME: 39.7551327 s

method {:test} Test14() {
var r0 := calcC(48);
expect r0 == C(48);
}

// REPEAT 8 - TIME: 40.9069119 s

method {:test} Test16() {
var r0 := calcC(49);
expect r0 == C(49);
}

// REPEAT 9 - TIME: 42.1243163 s

method {:test} Test18() {
var r0 := calcC(50);
expect r0 == C(50);
}

// REPEAT 10 - TIME: 43.4137203 s
