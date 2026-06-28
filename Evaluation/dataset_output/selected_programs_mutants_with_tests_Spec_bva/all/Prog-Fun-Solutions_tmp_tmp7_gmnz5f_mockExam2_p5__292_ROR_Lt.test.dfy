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
  while k < 0
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
method {:test} Test1() {
var r0 := problem5(100);
}
method {:test} Test3() {
var r0 := problem5(17);
}
method {:test} Test4() {
var r0 := problem5(5332);
}

// REPEAT 1 - TIME: 8.0219325 s

method {:test} Test7() {
var r0 := problem5(5333);
}

// REPEAT 2 - TIME: 9.1749143 s

method {:test} Test8() {
var r0 := problem5(5334);
}

// REPEAT 3 - TIME: 10.2376352 s

method {:test} Test9() {
var r0 := problem5(5337);
}

// REPEAT 4 - TIME: 11.2910013 s

method {:test} Test10() {
var r0 := problem5(5340);
}

// REPEAT 5 - TIME: 12.0941561 s

method {:test} Test11() {
var r0 := problem5(5343);
}

// REPEAT 6 - TIME: 12.9966769 s

method {:test} Test12() {
var r0 := problem5(5346);
}

// REPEAT 7 - TIME: 13.8892092 s

method {:test} Test13() {
var r0 := problem5(5349);
}

// REPEAT 8 - TIME: 14.6373832 s

method {:test} Test14() {
var r0 := problem5(5352);
}

// REPEAT 9 - TIME: 15.5967209 s

method {:test} Test15() {
var r0 := problem5(5355);
}

// REPEAT 10 - TIME: 16.6799133 s
