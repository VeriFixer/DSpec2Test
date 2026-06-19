// Prog-Fun-Solutions_tmp_tmp7_gmnz5f_extra_mod2.dfy

ghost function f2(n: nat): nat
{
  if n == 0 then
    0
  else
    5 * f2(n / 3) + n % 4
}

method {:testEntry} mod2(n: nat) returns (a: nat)
  ensures a == f2(n)
{
  var x: nat := 1;
  var y: nat := 0;
  var k: nat := n;
  while k >= 0
    invariant f2(n) == x * f2(k) + y
    invariant 0 <= k <= n
    decreases k
  {
    assert f2(n) == x * f2(k) + y;
    assert f2(n) == x * (5 * f2(k / 3) + k % 4) + y;
    assert f2(n) == 5 * x * f2(k / 3) + x * (k % 4) + y;
    y := x * (k % 4) + y;
    assert f2(n) == 5 * x * f2(k / 3) + y;
    x := 5 * x;
    assert f2(n) == x * f2(k / 3) + y;
    k := k / 3;
    assert f2(n) == x * f2(k) + y;
  }
  assert k == 0;
  assert f2(n) == x * f2(0) + y;
  assert f2(n) == x * 0 + y;
  assert f2(n) == y;
  a := y;
}


method {:test} Test0() {
var r0 := mod2(3);
}

// REPEAT 1 - TIME: 12.1013379 s

method {:test} Test1() {
var r0 := mod2(4);
}

// REPEAT 2 - TIME: 17.4432722 s

method {:test} Test2() {
var r0 := mod2(5);
}

// REPEAT 3 - TIME: 22.1520336 s

method {:test} Test3() {
var r0 := mod2(247644);
}

// REPEAT 4 - TIME: 26.7987273 s

method {:test} Test4() {
var r0 := mod2(247645);
}

// REPEAT 5 - TIME: 31.5000703 s

method {:test} Test5() {
var r0 := mod2(247646);
}

// REPEAT 6 - TIME: 36.6274547 s

method {:test} Test6() {
var r0 := mod2(247668);
}

// REPEAT 7 - TIME: 40.9503585 s

method {:test} Test7() {
var r0 := mod2(247669);
}

// REPEAT 8 - TIME: 46.5394415 s

method {:test} Test8() {
var r0 := mod2(247670);
}

// REPEAT 9 - TIME: 50.8648512 s

method {:test} Test9() {
var r0 := mod2(247672);
}

// REPEAT 10 - TIME: 56.1178641 s
