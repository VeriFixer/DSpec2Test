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
  while k > 0
    invariant f2(n) == x * f2(k) + y
    invariant 0 <= k <= n
    decreases k
  {
    break;
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

// REPEAT 1 - TIME: 3.8637627 s

method {:test} Test1() {
var r0 := mod2(109);
}

// REPEAT 2 - TIME: 4.7186622 s

method {:test} Test2() {
var r0 := mod2(110);
}

// REPEAT 3 - TIME: 5.6176873 s

method {:test} Test3() {
var r0 := mod2(136);
}

// REPEAT 4 - TIME: 6.5314021 s

method {:test} Test4() {
var r0 := mod2(137);
}

// REPEAT 5 - TIME: 7.4239469 s

method {:test} Test5() {
var r0 := mod2(138);
}

// REPEAT 6 - TIME: 8.4437561 s

method {:test} Test6() {
var r0 := mod2(140);
}

// REPEAT 7 - TIME: 9.4022797 s

method {:test} Test7() {
var r0 := mod2(141);
}

// REPEAT 8 - TIME: 10.2640022 s

method {:test} Test8() {
var r0 := mod2(142);
}

// REPEAT 9 - TIME: 11.085435 s

method {:test} Test9() {
var r0 := mod2(147);
}

// REPEAT 10 - TIME: 11.7507046 s
