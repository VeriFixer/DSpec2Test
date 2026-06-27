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
  while k >= 0
    invariant f(n) == a * f(k) + b
    invariant -5 <= k <= n
    decreases k
  {
    assert f(n) == a * f(k) + b;
    assert f(n) == a * (3 * f(k - 5) + k) + b;
    assert f(n) == 3 * a * f(k - 5) + a * k + b;
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
var r0 := problem5(1);
}

// REPEAT 1 - TIME: 5.3208548 s

method {:test} Test1() {
var r0 := problem5(2);
}

// REPEAT 2 - TIME: 8.9021303 s

method {:test} Test2() {
var r0 := problem5(3);
}

// REPEAT 3 - TIME: 11.4497912 s

method {:test} Test3() {
var r0 := problem5(4);
}

// REPEAT 4 - TIME: 13.9752453 s

method {:test} Test4() {
var r0 := problem5(1801);
}

// REPEAT 5 - TIME: 16.5160055 s

method {:test} Test5() {
var r0 := problem5(1803);
}

// REPEAT 6 - TIME: 19.2450725 s

method {:test} Test6() {
var r0 := problem5(1806);
}

// REPEAT 7 - TIME: 22.3304552 s

method {:test} Test7() {
var r0 := problem5(1809);
}

// REPEAT 8 - TIME: 24.8460003 s

method {:test} Test8() {
var r0 := problem5(1812);
}

// REPEAT 9 - TIME: 28.0323116 s

method {:test} Test9() {
var r0 := problem5(1815);
}

// REPEAT 10 - TIME: 30.9480277 s
