// Programmverifikation-und-synthese_tmp_tmppurk6ime_PVS_Assignment_ex_06_Hoangkim_ex_06_hoangkim.dfy

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
  var x: int;
  d := m;
  x := n;
  while false
    invariant x > 0
    invariant d > 0
    invariant gcd(d, x) == gcd(m, n)
    decreases x + d
  {
    if d > x {
      d := d - x;
    } else {
      x := x - d;
    }
  }
}

ghost function gcd'(x: int, y: int): int
  requires x > 0 && y > 0
  decreases if x > y then x else y
{
  if x == y then
    x
  else if x > y then
    gcd'(x - y, y)
  else
    gcd(y, x)
}

method {:test} Test16() {
expect 16843 > 0 && 8421 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16843, 8421);
}

// REPEAT 8 - TIME: 15.3024039 s
