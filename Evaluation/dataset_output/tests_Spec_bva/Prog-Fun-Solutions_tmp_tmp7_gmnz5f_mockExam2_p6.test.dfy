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
var r0 := problem6(100);
}
method {:test} Test2() {
var r0 := problem6(2);
}
method {:test} Test3() {
var r0 := problem6(3000);
}

// REPEAT 1 - TIME: 8.5896152 s

method {:test} Test7() {
var r0 := problem6(3001);
}

// REPEAT 2 - TIME: 9.8375855 s

method {:test} Test8() {
var r0 := problem6(11100);
}

// REPEAT 3 - TIME: 10.9360524 s

method {:test} Test9() {
var r0 := problem6(11101);
}

// REPEAT 4 - TIME: 12.0544995 s

method {:test} Test10() {
var r0 := problem6(19200);
}

// REPEAT 5 - TIME: 13.2074752 s

method {:test} Test11() {
var r0 := problem6(19201);
}

// REPEAT 6 - TIME: 14.2999822 s

method {:test} Test12() {
var r0 := problem6(19202);
}

// REPEAT 7 - TIME: 15.3250819 s

method {:test} Test13() {
var r0 := problem6(19203);
}

// REPEAT 8 - TIME: 16.286826 s

method {:test} Test14() {
var r0 := problem6(19204);
}

// REPEAT 9 - TIME: 17.2127366 s

method {:test} Test15() {
var r0 := problem6(19205);
}

// REPEAT 10 - TIME: 18.1009446 s
