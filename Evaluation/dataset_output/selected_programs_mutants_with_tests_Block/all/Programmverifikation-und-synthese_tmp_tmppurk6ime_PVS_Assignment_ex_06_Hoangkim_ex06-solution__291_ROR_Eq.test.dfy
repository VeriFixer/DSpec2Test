// Programmverifikation-und-synthese_tmp_tmppurk6ime_PVS_Assignment_ex_06_Hoangkim_ex06-solution.dfy

ghost function gcd(x: int, y: int): int
  requires x > 0 && y > 0
{
  if x == y then
    x
  else if x > y then
    gcd(x - y, y)
  else
    gcd(x, y - x)
}

method {:testEntry} gcdI(m: int, n: int) returns (d: int)
  requires m > 0 && n > 0
  ensures d == gcd(m, n)
{
  var x, y := m, n;
  d := 1;
  while x == y
    invariant x > 0 && y > 0
    invariant gcd(x, y) == gcd(m, n)
    decreases x + y
  {
    if x > y {
      x := x - y;
    } else {
      y := y - x;
    }
  }
  d := x;
}

ghost function gcd'(x: int, y: int): int
  requires x > 0 && y > 0
  decreases x + y, y
{
  if x == y then
    x
  else if x > y then
    gcd'(x - y, y)
  else
    gcd'(y, x)
}


method {:test} Test0() {
expect 39 > 0 && 1315 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(39, 1315);
}
method {:test} Test1() {
expect 103 > 0 && 12602 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(103, 12602);
}
method {:test} Test2() {
expect 3369 > 0 && 14970 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(3369, 14970);
}

// REPEAT 1 - TIME: 3.5223301 s

method {:test} Test3() {
expect 3370 > 0 && 14971 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(3370, 14971);
}

// REPEAT 2 - TIME: 5.5548993 s

method {:test} Test6() {
expect 3371 > 0 && 14972 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(3371, 14972);
}
method {:test} Test7() {
expect 8722 > 0 && 17444 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(8722, 17444);
}

// REPEAT 3 - TIME: 7.2772264 s

method {:test} Test9() {
expect 8723 > 0 && 25166 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(8723, 25166);
}
method {:test} Test10() {
expect 8723 > 0 && 17446 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(8723, 17446);
}
method {:test} Test11() {
expect 16442 > 0 && 32884 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16442, 32884);
}

// REPEAT 4 - TIME: 9.0106497 s

method {:test} Test12() {
expect 16443 > 0 && 32886 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16443, 32886);
}
method {:test} Test13() {
expect 16443 > 0 && 35324 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16443, 35324);
}

// REPEAT 5 - TIME: 10.6708282 s

method {:test} Test15() {
expect 17701 > 0 && 35402 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(17701, 35402);
}
method {:test} Test16() {
expect 16444 > 0 && 35325 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16444, 35325);
}

// REPEAT 6 - TIME: 12.0859832 s

method {:test} Test18() {
expect 17702 > 0 && 35404 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(17702, 35404);
}

// REPEAT 7 - TIME: 13.3164509 s

method {:test} Test21() {
expect 17703 > 0 && 43126 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(17703, 43126);
}
method {:test} Test22() {
expect 17703 > 0 && 37844 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(17703, 37844);
}
method {:test} Test23() {
expect 17703 > 0 && 44262 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(17703, 44262);
}

// REPEAT 8 - TIME: 14.4797713 s

method {:test} Test24() {
expect 22170 > 0 && 44340 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(22170, 44340);
}
method {:test} Test25() {
expect 23368 > 0 && 46736 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23368, 46736);
}

// REPEAT 9 - TIME: 15.5756238 s

method {:test} Test27() {
expect 23369 > 0 && 54458 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23369, 54458);
}
method {:test} Test28() {
expect 23369 > 0 && 55594 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23369, 55594);
}
method {:test} Test29() {
expect 23369 > 0 && 49176 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23369, 49176);
}

// REPEAT 10 - TIME: 16.4851223 s
