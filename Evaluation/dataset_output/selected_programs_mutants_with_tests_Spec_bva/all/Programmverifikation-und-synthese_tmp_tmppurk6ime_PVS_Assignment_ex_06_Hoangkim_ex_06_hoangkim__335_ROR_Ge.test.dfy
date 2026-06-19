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
  while d >= x
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
expect 16677 > 0 && 7720 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16677, 7720);
}
method {:test} Test1() {
expect 1 > 0 && 1239 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(1, 1239);
}
method {:test} Test2() {
expect 100 > 0 && 201 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(100, 201);
}
method {:test} Test3() {
expect 1239 > 0 && 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(1239, 1);
}
method {:test} Test4() {
expect 201 > 0 && 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(201, 100);
}

// REPEAT 1 - TIME: 7.5176437 s

method {:test} Test10() {
expect 16754 > 0 && 8377 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16754, 8377);
}

// REPEAT 2 - TIME: 8.6202805 s

method {:test} Test11() {
expect 16757 > 0 && 8378 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16757, 8378);
}

// REPEAT 3 - TIME: 9.5303864 s

method {:test} Test12() {
expect 16759 > 0 && 8379 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16759, 8379);
}

// REPEAT 4 - TIME: 10.4113707 s

method {:test} Test13() {
expect 16836 > 0 && 8418 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16836, 8418);
}

// REPEAT 5 - TIME: 11.2078811 s

method {:test} Test14() {
expect 16838 > 0 && 8419 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16838, 8419);
}

// REPEAT 6 - TIME: 12.0265347 s

method {:test} Test15() {
expect 16840 > 0 && 8420 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16840, 8420);
}

// REPEAT 7 - TIME: 12.7693958 s

method {:test} Test16() {
expect 16843 > 0 && 8421 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16843, 8421);
}

// REPEAT 8 - TIME: 13.5449195 s

method {:test} Test17() {
expect 16845 > 0 && 8422 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16845, 8422);
}

// REPEAT 9 - TIME: 14.4097385 s

method {:test} Test18() {
expect 16847 > 0 && 8423 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16847, 8423);
}

// REPEAT 10 - TIME: 15.062213 s
