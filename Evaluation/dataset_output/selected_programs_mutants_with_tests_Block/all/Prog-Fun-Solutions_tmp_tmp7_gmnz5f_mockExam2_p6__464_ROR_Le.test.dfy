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
  while k <= n
    invariant 0 <= k <= n && x == f(k) && y == f(k + 1) && a == fSum(k)
    decreases n - k
  {
    assert x == f(k) && y == f(k + 1) && a == fSum(k);
    k := k + 1;
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

// REPEAT 1 - TIME: 3.4539733 s

method {:test} Test2() {
var r0 := problem6(6);
}
method {:test} Test3() {
var r0 := problem6(2);
}

// REPEAT 2 - TIME: 5.277962 s

method {:test} Test4() {
var r0 := problem6(9);
}
method {:test} Test5() {
var r0 := problem6(7);
}

// REPEAT 3 - TIME: 7.1397708 s

method {:test} Test6() {
var r0 := problem6(76);
}
method {:test} Test7() {
var r0 := problem6(10);
}

// REPEAT 4 - TIME: 9.0101805 s

method {:test} Test8() {
var r0 := problem6(77);
}

// REPEAT 5 - TIME: 39.9364505 s

method {:test} Test9() {
var r0 := problem6(98);
}
method {:test} Test10() {
var r0 := problem6(78);
}

// REPEAT 6 - TIME: 41.0811491 s

method {:test} Test11() {
var r0 := problem6(99);
}

// REPEAT 7 - TIME: 42.1392895 s

method {:test} Test13() {
var r0 := problem6(100);
}

// REPEAT 8 - TIME: 43.1942628 s

method {:test} Test15() {
var r0 := problem6(101);
}

// REPEAT 9 - TIME: 44.4519042 s

method {:test} Test17() {
var r0 := problem6(102);
}

// REPEAT 10 - TIME: 45.829987 s
