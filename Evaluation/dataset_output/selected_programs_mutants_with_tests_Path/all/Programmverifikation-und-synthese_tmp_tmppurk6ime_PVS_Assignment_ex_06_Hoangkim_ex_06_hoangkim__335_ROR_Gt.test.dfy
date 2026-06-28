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
  while d > x
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


method {:test} Test0() {
expect 2 > 0 && 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(2, 1);
}

// REPEAT 1 - TIME: 6.062323 s

method {:test} Test1() {
expect 7724 > 0 && 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7724, 2);
}

// REPEAT 2 - TIME: 9.7858342 s

method {:test} Test2() {
expect 7725 > 0 && 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7725, 3);
}

// REPEAT 3 - TIME: 13.1656716 s

method {:test} Test3() {
expect 7726 > 0 && 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7726, 4);
}

// REPEAT 4 - TIME: 16.7240461 s

method {:test} Test4() {
expect 7727 > 0 && 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7727, 5);
}

// REPEAT 5 - TIME: 20.5971628 s

method {:test} Test5() {
expect 7728 > 0 && 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7728, 9);
}

// REPEAT 6 - TIME: 23.7651215 s

method {:test} Test6() {
expect 7729 > 0 && 19 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7729, 19);
}

// REPEAT 7 - TIME: 27.1254485 s

method {:test} Test7() {
expect 23168 > 0 && 11584 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23168, 11584);
}

// REPEAT 8 - TIME: 30.4301123 s

method {:test} Test8() {
expect 23170 > 0 && 11585 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23170, 11585);
}

// REPEAT 9 - TIME: 33.963468 s

method {:test} Test9() {
expect 23172 > 0 && 11586 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23172, 11586);
}

// REPEAT 10 - TIME: 37.373113 s
