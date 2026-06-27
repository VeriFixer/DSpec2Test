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
  while x > y
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
