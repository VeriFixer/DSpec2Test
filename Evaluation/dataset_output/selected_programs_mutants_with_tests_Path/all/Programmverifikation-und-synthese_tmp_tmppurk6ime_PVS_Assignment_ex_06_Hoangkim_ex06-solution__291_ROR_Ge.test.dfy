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
  while x >= y
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

// REPEAT 1 - TIME: 5.7620919 s

method {:test} Test1() {
expect 40 > 0 && 1316 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(40, 1316);
}

// REPEAT 2 - TIME: 9.4128389 s

method {:test} Test2() {
expect 41 > 0 && 1317 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(41, 1317);
}

// REPEAT 3 - TIME: 12.672074 s

method {:test} Test3() {
expect 42 > 0 && 1318 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(42, 1318);
}

// REPEAT 4 - TIME: 15.6531916 s

method {:test} Test4() {
expect 43 > 0 && 1319 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(43, 1319);
}

// REPEAT 5 - TIME: 18.8607882 s

method {:test} Test5() {
expect 44 > 0 && 1320 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(44, 1320);
}

// REPEAT 6 - TIME: 22.1138163 s

method {:test} Test6() {
expect 45 > 0 && 1321 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(45, 1321);
}

// REPEAT 7 - TIME: 25.6337164 s

method {:test} Test7() {
expect 46 > 0 && 1322 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(46, 1322);
}

// REPEAT 8 - TIME: 29.2856268 s

method {:test} Test8() {
expect 47 > 0 && 1323 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(47, 1323);
}

// REPEAT 9 - TIME: 33.0256277 s

method {:test} Test9() {
expect 48 > 0 && 1324 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(48, 1324);
}

// REPEAT 10 - TIME: 36.1525689 s
