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
  while k <= 0
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
var r0 := mod2(775116);
}

// REPEAT 1 - TIME: 5.900282 s

method {:test} Test1() {
var r0 := mod2(775117);
}

// REPEAT 2 - TIME: 6.9298925 s

method {:test} Test2() {
var r0 := mod2(775118);
}

// REPEAT 3 - TIME: 7.9381905 s

method {:test} Test3() {
var r0 := mod2(775119);
}

// REPEAT 4 - TIME: 8.9243652 s

method {:test} Test4() {
var r0 := mod2(775128);
}

// REPEAT 5 - TIME: 10.0349478 s

method {:test} Test5() {
var r0 := mod2(775140);
}

// REPEAT 6 - TIME: 10.9750682 s

method {:test} Test6() {
var r0 := mod2(775141);
}

// REPEAT 7 - TIME: 11.7402176 s

method {:test} Test7() {
var r0 := mod2(775152);
}

// REPEAT 8 - TIME: 12.5575689 s

method {:test} Test8() {
var r0 := mod2(775153);
}

// REPEAT 9 - TIME: 13.36601 s

method {:test} Test9() {
var r0 := mod2(775154);
}

// REPEAT 10 - TIME: 14.084488 s
