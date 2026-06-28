// Prog-Fun-Solutions_tmp_tmp7_gmnz5f_mockExam2_p5.dfy

ghost function f(n: int): int
{
  if n < 0 then
    0
  else
    3 * f(n - 5) + n
}

method {:testEntry} problem5(n: nat) returns (x: int)
  ensures x == f(n)
{
  var a := 1;
  var b := 0;
  var k := n;
  while true
    invariant f(n) == a * f(k) + b
    invariant -5 <= k <= n
    decreases k
  {
    assert f(n) == a * f(k) + b;
    assert f(n) == a * (3 * f(k - 5) + k) + b;
    assert f(n) == 3 * a * f(k - 5) + a * k + b;
    b := a * k + b;
    assert f(n) == 3 * a * f(k - 5) + b;
    a := 3 * a;
    assert f(n) == a * f(k - 5) + b;
    k := k - 5;
    assert f(n) == a * f(k) + b;
  }
  assert k < 0;
  assert f(n) == a * f(k) + b;
  assert f(n) == a * 0 + b;
  x := b;
  assert x == f(n);
}


method {:test} Test0() {
var r0 := problem5(3);
}

// REPEAT 1 - TIME: 3.0721664 s

method {:test} Test1() {
var r0 := problem5(4);
}

// REPEAT 2 - TIME: 4.0651685 s

method {:test} Test2() {
var r0 := problem5(2442);
}

// REPEAT 3 - TIME: 5.140599 s

method {:test} Test3() {
var r0 := problem5(2445);
}

// REPEAT 4 - TIME: 6.1764831 s

method {:test} Test4() {
var r0 := problem5(2448);
}

// REPEAT 5 - TIME: 7.3381725 s

method {:test} Test5() {
var r0 := problem5(2451);
}

// REPEAT 6 - TIME: 8.2520357 s

method {:test} Test6() {
var r0 := problem5(2454);
}

// REPEAT 7 - TIME: 9.1693303 s

method {:test} Test7() {
var r0 := problem5(2457);
}

// REPEAT 8 - TIME: 9.9038829 s

method {:test} Test8() {
var r0 := problem5(2460);
}

// REPEAT 9 - TIME: 10.5554847 s

method {:test} Test9() {
var r0 := problem5(2463);
}

// REPEAT 10 - TIME: 11.0746001 s
