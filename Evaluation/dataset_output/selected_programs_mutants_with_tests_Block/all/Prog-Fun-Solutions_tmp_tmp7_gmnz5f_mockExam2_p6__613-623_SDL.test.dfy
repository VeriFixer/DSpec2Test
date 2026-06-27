// Prog-Fun-Solutions_tmp_tmp7_gmnz5f_mockExam2_p6.dfy

ghost function f(n: int): int
{
  if n <= 0 then
    1
  else
    n + f(n - 1) * f(n - 2)
}

ghost function fSum(n: nat): int
{
  if n <= 0 then
    0
  else
    f(n - 1) + fSum(n - 1)
}

method {:testEntry} problem6(n: nat) returns (a: int)
  ensures a == fSum(n)
{
  a := 0;
  var k := 0;
  var x := 1;
  var y := 2;
  while k < n
    invariant 0 <= k <= n && x == f(k) && y == f(k + 1) && a == fSum(k)
    decreases n - k
  {
    assert x == f(k) && y == f(k + 1) && a == fSum(k);
    assert x == f(k - 1) && y == f(k) && a == fSum(k - 1);
    assert x == f(k - 1) && y == f(k) && a == fSum(k) - f(k - 1);
    a := a + x;
    assert x == f(k - 1) && y == f(k) && a == fSum(k) - f(k - 1) + f(k - 1);
    assert x == f(k - 1) && y == f(k) && a == fSum(k);
    x, y := y, k + 1 + x * y;
    assert x == f(k) && y == k + 1 + f(k - 1) * f(k) && a == fSum(k);
    assert x == f(k) && y == k + 1 + f(k + 1 - 2) * f(k + 1 - 1) && a == fSum(k);
    assert x == f(k) && y == f(k + 1) && a == fSum(k);
  }
  assert a == fSum(k);
}


method {:test} Test0() {
var r0 := problem6(0);
}
method {:test} Test1() {
var r0 := problem6(1);
}

// REPEAT 1 - TIME: 3.6051308 s

method {:test} Test2() {
var r0 := problem6(2);
}

// REPEAT 2 - TIME: 5.3308715 s

method {:test} Test4() {
var r0 := problem6(6);
}
method {:test} Test5() {
var r0 := problem6(3);
}

// REPEAT 3 - TIME: 7.151406 s

method {:test} Test6() {
var r0 := problem6(7);
}

// REPEAT 4 - TIME: 8.6356368 s

method {:test} Test8() {
var r0 := problem6(8);
}

// REPEAT 5 - TIME: 39.5610422 s

method {:test} Test9() {
var r0 := problem6(9);
}

// REPEAT 6 - TIME: 40.5662995 s

method {:test} Test11() {
var r0 := problem6(48);
}
method {:test} Test12() {
var r0 := problem6(10);
}

// REPEAT 7 - TIME: 41.5965443 s

method {:test} Test13() {
var r0 := problem6(6751);
}
method {:test} Test14() {
var r0 := problem6(49);
}

// REPEAT 8 - TIME: 42.858076 s

method {:test} Test15() {
var r0 := problem6(13503);
}
method {:test} Test16() {
var r0 := problem6(6752);
}

// REPEAT 9 - TIME: 44.007377 s

method {:test} Test17() {
var r0 := problem6(13504);
}

// REPEAT 10 - TIME: 45.3131227 s
