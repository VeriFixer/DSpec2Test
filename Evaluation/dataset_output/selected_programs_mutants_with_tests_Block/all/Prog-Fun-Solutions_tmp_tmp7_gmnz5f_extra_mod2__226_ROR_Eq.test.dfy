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
  while k == 0
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
var r0 := mod2(108);
}

// REPEAT 1 - TIME: 4.726304 s

method {:test} Test1() {
var r0 := mod2(109);
}

// REPEAT 2 - TIME: 5.76135 s

method {:test} Test2() {
var r0 := mod2(110);
}

// REPEAT 3 - TIME: 6.7773512 s

method {:test} Test3() {
var r0 := mod2(136);
}

// REPEAT 4 - TIME: 8.0212655 s

method {:test} Test4() {
var r0 := mod2(137);
}

// REPEAT 5 - TIME: 9.1591224 s

method {:test} Test5() {
var r0 := mod2(138);
}

// REPEAT 6 - TIME: 10.3663317 s

method {:test} Test6() {
var r0 := mod2(140);
}

// REPEAT 7 - TIME: 11.2420497 s

method {:test} Test7() {
var r0 := mod2(141);
}

// REPEAT 8 - TIME: 12.1589738 s

method {:test} Test8() {
var r0 := mod2(142);
}

// REPEAT 9 - TIME: 12.9157891 s

method {:test} Test9() {
var r0 := mod2(147);
}

// REPEAT 10 - TIME: 13.6978208 s
