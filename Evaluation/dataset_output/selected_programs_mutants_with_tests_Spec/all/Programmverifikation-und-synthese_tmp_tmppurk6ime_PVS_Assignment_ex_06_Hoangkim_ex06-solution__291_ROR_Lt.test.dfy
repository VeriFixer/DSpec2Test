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
  while x < y
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
expect 16677 > 0 && 7720 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16677, 7720);
}

// REPEAT 1 - TIME: 3.1663405 s

method {:test} Test1() {
expect 16678 > 0 && 7721 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16678, 7721);
}

// REPEAT 2 - TIME: 4.2094699 s

method {:test} Test2() {
expect 16679 > 0 && 7722 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16679, 7722);
}

// REPEAT 3 - TIME: 5.1437621 s

method {:test} Test3() {
expect 16680 > 0 && 7723 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16680, 7723);
}

// REPEAT 4 - TIME: 6.0811669 s

method {:test} Test4() {
expect 16758 > 0 && 8379 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16758, 8379);
}

// REPEAT 5 - TIME: 6.9745611 s

method {:test} Test5() {
expect 16761 > 0 && 8380 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16761, 8380);
}

// REPEAT 6 - TIME: 8.0037252 s

method {:test} Test6() {
expect 16763 > 0 && 8381 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16763, 8381);
}

// REPEAT 7 - TIME: 8.9919749 s

method {:test} Test7() {
expect 16840 > 0 && 8420 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16840, 8420);
}

// REPEAT 8 - TIME: 9.8465997 s

method {:test} Test8() {
expect 16842 > 0 && 8421 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16842, 8421);
}

// REPEAT 9 - TIME: 10.8887765 s

method {:test} Test9() {
expect 16844 > 0 && 8422 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16844, 8422);
}

// REPEAT 10 - TIME: 11.7751882 s
