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
  while false
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

// REPEAT 1 - TIME: 7.8780565 s

method {:test} Test1() {
expect 40 > 0 && 1316 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(40, 1316);
}

// REPEAT 2 - TIME: 12.4880843 s

method {:test} Test2() {
expect 697 > 0 && 1394 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(697, 1394);
}

// REPEAT 3 - TIME: 17.1178807 s

method {:test} Test3() {
expect 698 > 0 && 9116 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(698, 9116);
}

// REPEAT 4 - TIME: 21.8666907 s

method {:test} Test4() {
expect 4597 > 0 && 9194 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(4597, 9194);
}

// REPEAT 5 - TIME: 26.8214541 s

method {:test} Test5() {
expect 4598 > 0 && 16916 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(4598, 16916);
}

// REPEAT 6 - TIME: 31.05784 s

method {:test} Test6() {
expect 8497 > 0 && 16994 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(8497, 16994);
}

// REPEAT 7 - TIME: 35.6209291 s

method {:test} Test7() {
expect 8498 > 0 && 16996 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(8498, 16996);
}

// REPEAT 8 - TIME: 40.0470485 s

method {:test} Test8() {
expect 8499 > 0 && 24718 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(8499, 24718);
}

// REPEAT 9 - TIME: 44.9959313 s

method {:test} Test9() {
expect 8500 > 0 && 24719 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(8500, 24719);
}

// REPEAT 10 - TIME: 49.1748911 s
