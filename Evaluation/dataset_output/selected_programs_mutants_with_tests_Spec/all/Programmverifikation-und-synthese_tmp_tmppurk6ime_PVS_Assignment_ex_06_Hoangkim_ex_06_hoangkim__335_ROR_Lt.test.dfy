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
  while d < x
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

// REPEAT 1 - TIME: 3.0800592 s

method {:test} Test1() {
expect 16678 > 0 && 7721 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16678, 7721);
}

// REPEAT 2 - TIME: 4.2107017 s

method {:test} Test2() {
expect 16679 > 0 && 7722 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16679, 7722);
}

// REPEAT 3 - TIME: 5.1965891 s

method {:test} Test3() {
expect 16756 > 0 && 8378 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16756, 8378);
}

// REPEAT 4 - TIME: 6.3361845 s

method {:test} Test4() {
expect 16759 > 0 && 8379 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16759, 8379);
}

// REPEAT 5 - TIME: 7.4719369 s

method {:test} Test5() {
expect 16836 > 0 && 8418 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16836, 8418);
}

// REPEAT 6 - TIME: 8.5022364 s

method {:test} Test6() {
expect 16839 > 0 && 8419 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16839, 8419);
}

// REPEAT 7 - TIME: 9.4664927 s

method {:test} Test7() {
expect 16841 > 0 && 8420 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16841, 8420);
}

// REPEAT 8 - TIME: 10.448123 s

method {:test} Test8() {
expect 16918 > 0 && 8459 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16918, 8459);
}

// REPEAT 9 - TIME: 11.2512045 s

method {:test} Test9() {
expect 16921 > 0 && 8460 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16921, 8460);
}

// REPEAT 10 - TIME: 12.0814506 s
