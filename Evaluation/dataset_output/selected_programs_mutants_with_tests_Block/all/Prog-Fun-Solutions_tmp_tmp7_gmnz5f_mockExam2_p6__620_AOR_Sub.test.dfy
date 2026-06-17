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
    k := k - 1;
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


// problem 6:
// name:      Gabriele Berardi
// s-number: s4878728
// table:     XXXXX

ghost function f(n: int): int {
  if n <= 0 then 1 else n + f(n-1)*f(n-2)
}

ghost function fSum(n: nat): int {
 // give the body of this function
  // it should return Sum(i: 0<=i < n: f(i))
  if n <= 0 then 0 else f(n-1) + fSum(n-1)
}

method {:testEntry} problem6(n:nat) returns (a: int)
ensures a == fSum(n)
{
  a := 0;
  var k := 0;
  var x := 1;
  var y := 2;
  while k < n
  invariant 0 <= k <= n && x == f(k) && y == f(k+1) && a == fSum(k)
  decreases n-k
  {
    assert x == f(k) && y == f(k+1) && a == fSum(k);
    k := k + 1;
    assert x == f(k-1) && y == f(k) && a == fSum(k-1);
    assert x == f(k-1) && y == f(k) && a == fSum(k) - f(k-1);
    a := a + x;
    assert x == f(k-1) && y == f(k) && a == fSum(k) - f(k-1) + f(k-1);
    assert x == f(k-1) && y == f(k) && a == fSum(k);

    x, y := y, k+1 + x*y;    
    assert x == f(k) && y == k+1+f(k-1)*f(k) && a == fSum(k);
    assert x == f(k) && y == k+1+f(k+1-2)*f(k+1-1) && a == fSum(k);
    assert x == f(k) && y == f(k+1) && a == fSum(k);
  }
  assert a == fSum(k);
}

method {:test} Test0() {
var r0 := problem6(0);
}
method {:test} Test1() {
var r0 := problem6(1);
}

// REPEAT 1 - TIME: 2.9040798 s

method {:test} Test2() {
var r0 := problem6(2);
}

// REPEAT 2 - TIME: 4.1665851 s

method {:test} Test4() {
var r0 := problem6(6);
}
method {:test} Test5() {
var r0 := problem6(3);
}

// REPEAT 3 - TIME: 5.5836911 s

method {:test} Test6() {
var r0 := problem6(39);
}
method {:test} Test7() {
var r0 := problem6(7);
}

// REPEAT 4 - TIME: 6.7775307 s

method {:test} Test8() {
var r0 := problem6(47);
}
method {:test} Test9() {
var r0 := problem6(40);
}

// REPEAT 5 - TIME: 8.5682595 s

method {:test} Test10() {
var r0 := problem6(48);
}

// REPEAT 6 - TIME: 9.8390513 s

method {:test} Test12() {
var r0 := problem6(49);
}

// REPEAT 7 - TIME: 11.2907841 s

method {:test} Test14() {
var r0 := problem6(51);
}
method {:test} Test15() {
var r0 := problem6(50);
}

// REPEAT 8 - TIME: 12.7155962 s

method {:test} Test16() {
var r0 := problem6(53);
}
method {:test} Test17() {
var r0 := problem6(52);
}

// REPEAT 9 - TIME: 14.194945 s

method {:test} Test18() {
var r0 := problem6(54);
}

// REPEAT 10 - TIME: 15.2868604 s
