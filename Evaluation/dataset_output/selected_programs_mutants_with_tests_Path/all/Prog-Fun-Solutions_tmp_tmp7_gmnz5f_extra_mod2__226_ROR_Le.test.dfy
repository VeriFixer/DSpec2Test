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
var r0 := mod2(3);
}

// REPEAT 1 - TIME: 8.820102 s

method {:test} Test1() {
var r0 := mod2(4);
}

// REPEAT 2 - TIME: 12.4666447 s

method {:test} Test2() {
var r0 := mod2(5);
}

// REPEAT 3 - TIME: 15.7676715 s

method {:test} Test3() {
var r0 := mod2(295992);
}

// REPEAT 4 - TIME: 19.044914 s

method {:test} Test4() {
var r0 := mod2(295993);
}

// REPEAT 5 - TIME: 22.5775165 s

method {:test} Test5() {
var r0 := mod2(295994);
}

// REPEAT 6 - TIME: 26.3690672 s

method {:test} Test6() {
var r0 := mod2(296016);
}

// REPEAT 7 - TIME: 30.0946707 s

method {:test} Test7() {
var r0 := mod2(296017);
}

// REPEAT 8 - TIME: 33.7213999 s

method {:test} Test8() {
var r0 := mod2(296018);
}

// REPEAT 9 - TIME: 37.1486381 s

method {:test} Test9() {
var r0 := mod2(296020);
}

// REPEAT 10 - TIME: 40.3467206 s
