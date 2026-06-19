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

// REPEAT 1 - TIME: 2.8607306 s

method {:test} Test1() {
var r0 := problem6(2);
}

// REPEAT 2 - TIME: 4.039353 s

method {:test} Test2() {
var r0 := problem6(6286);
}

// REPEAT 3 - TIME: 4.9866383 s

method {:test} Test3() {
var r0 := problem6(6287);
}

// REPEAT 4 - TIME: 6.0802907 s

method {:test} Test4() {
var r0 := problem6(6288);
}

// REPEAT 5 - TIME: 7.1985887 s

method {:test} Test5() {
var r0 := problem6(6289);
}

// REPEAT 6 - TIME: 8.1701049 s

method {:test} Test6() {
var r0 := problem6(14388);
}

// REPEAT 7 - TIME: 8.9849718 s

method {:test} Test7() {
var r0 := problem6(14389);
}

// REPEAT 8 - TIME: 9.7183282 s

method {:test} Test8() {
var r0 := problem6(22488);
}

// REPEAT 9 - TIME: 10.4040832 s

method {:test} Test9() {
var r0 := problem6(22489);
}

// REPEAT 10 - TIME: 11.220849 s
