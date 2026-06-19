// Prog-Fun-Solutions_tmp_tmp7_gmnz5f_extra_pow.dfy

ghost function pow(a: int, e: nat): int
{
  if e == 0 then
    1
  else
    a * pow(a, e - 1)
}

method {:testEntry} Pow(a: nat, n: nat) returns (y: nat)
  ensures y == pow(a, n)
{
  var x: nat := 1;
  var k: nat := 0;
  while k < n
    invariant x == pow(a, k)
    invariant 0 <= k <= n
    decreases n - k
  {
    assert x == pow(a, k);
    assert x == a * pow(a, k);
    assert x == pow(a, k + 1);
    k := k + 1;
    assert x == pow(a, k);
  }
  assert k == n;
  y := x;
  assert y == pow(a, n);
}


method {:test} Test0() {
var r0 := Pow(0, 8100);
}

// REPEAT 1 - TIME: 2.8466858 s

method {:test} Test1() {
var r0 := Pow(1, 8101);
}

// REPEAT 2 - TIME: 3.8423115 s

method {:test} Test2() {
var r0 := Pow(283, 8102);
}

// REPEAT 3 - TIME: 4.8780914 s

method {:test} Test3() {
var r0 := Pow(284, 8103);
}

// REPEAT 4 - TIME: 5.9958713 s

method {:test} Test4() {
var r0 := Pow(285, 8104);
}

// REPEAT 5 - TIME: 7.1198033 s

method {:test} Test5() {
var r0 := Pow(286, 8105);
}

// REPEAT 6 - TIME: 8.147754 s

method {:test} Test6() {
var r0 := Pow(287, 8106);
}

// REPEAT 7 - TIME: 9.00937 s

method {:test} Test7() {
var r0 := Pow(288, 8107);
}

// REPEAT 8 - TIME: 9.9355607 s

method {:test} Test8() {
var r0 := Pow(289, 8108);
}

// REPEAT 9 - TIME: 10.9141384 s

method {:test} Test9() {
var r0 := Pow(290, 8109);
}

// REPEAT 10 - TIME: 11.6777752 s
