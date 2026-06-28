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
  while d <= x
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
expect 17714 > 0 && 8857 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(17714, 8857);
}
method {:test} Test1() {
expect 13725 > 0 && 6291 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(13725, 6291);
}

// REPEAT 1 - TIME: 3.0375279 s

method {:test} Test2() {
expect 17716 > 0 && 8858 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(17716, 8858);
}

// REPEAT 2 - TIME: 4.5385464 s

method {:test} Test4() {
expect 18955 > 0 && 8859 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(18955, 8859);
}
method {:test} Test5() {
expect 17718 > 0 && 17717 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(17718, 17717);
}

// REPEAT 3 - TIME: 6.1762226 s

method {:test} Test6() {
expect 36673 > 0 && 17718 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(36673, 17718);
}
method {:test} Test7() {
expect 44292 > 0 && 17718 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(44292, 17718);
}

// REPEAT 4 - TIME: 8.1754569 s

method {:test} Test8() {
expect 59732 > 0 && 29866 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(59732, 29866);
}
method {:test} Test9() {
expect 44293 > 0 && 17719 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(44293, 17719);
}

// REPEAT 5 - TIME: 9.4840285 s

method {:test} Test10() {
expect 60971 > 0 && 29867 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(60971, 29867);
}
method {:test} Test11() {
expect 59734 > 0 && 29867 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(59734, 29867);
}

// REPEAT 6 - TIME: 10.5552917 s

method {:test} Test12() {
expect 60972 > 0 && 29868 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(60972, 29868);
}

// REPEAT 7 - TIME: 11.7532528 s

method {:test} Test14() {
expect 60973 > 0 && 29869 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(60973, 29869);
}

// REPEAT 8 - TIME: 12.8775227 s

method {:test} Test16() {
expect 76412 > 0 && 38206 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(76412, 38206);
}
method {:test} Test17() {
expect 60974 > 0 && 29870 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(60974, 29870);
}

// REPEAT 9 - TIME: 13.8041435 s

method {:test} Test18() {
expect 77651 > 0 && 38207 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(77651, 38207);
}
method {:test} Test19() {
expect 78852 > 0 && 38207 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(78852, 38207);
}

// REPEAT 10 - TIME: 15.0227438 s
