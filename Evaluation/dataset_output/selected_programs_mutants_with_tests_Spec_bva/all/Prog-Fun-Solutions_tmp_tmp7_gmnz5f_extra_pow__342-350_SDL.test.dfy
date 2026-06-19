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
method {:test} Test1() {
var r0 := Pow(100, 2439);
}
method {:test} Test2() {
var r0 := Pow(2282, 100);
}
method {:test} Test4() {
var r0 := Pow(1, 842);
}
method {:test} Test5() {
var r0 := Pow(5853, 1144);
}

// REPEAT 1 - TIME: 6.9257822 s

method {:test} Test7() {
var r0 := Pow(5854, 8101);
}

// REPEAT 2 - TIME: 7.873605 s

method {:test} Test8() {
var r0 := Pow(5855, 8102);
}

// REPEAT 3 - TIME: 8.8666998 s

method {:test} Test9() {
var r0 := Pow(5856, 8103);
}

// REPEAT 4 - TIME: 9.5587788 s

method {:test} Test10() {
var r0 := Pow(5857, 8104);
}

// REPEAT 5 - TIME: 10.316416 s

method {:test} Test11() {
var r0 := Pow(5858, 8105);
}

// REPEAT 6 - TIME: 11.2466422 s

method {:test} Test12() {
var r0 := Pow(5859, 8106);
}

// REPEAT 7 - TIME: 12.0096442 s

method {:test} Test13() {
var r0 := Pow(5860, 8107);
}

// REPEAT 8 - TIME: 12.8156071 s

method {:test} Test14() {
var r0 := Pow(5861, 8108);
}

// REPEAT 9 - TIME: 13.6671123 s

method {:test} Test15() {
var r0 := Pow(5862, 8109);
}

// REPEAT 10 - TIME: 14.3920855 s
