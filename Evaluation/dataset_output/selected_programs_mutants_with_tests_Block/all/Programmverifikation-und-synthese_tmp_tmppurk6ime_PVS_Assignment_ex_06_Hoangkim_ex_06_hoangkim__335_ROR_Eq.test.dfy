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
  while d == x
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

// REPEAT 1 - TIME: 2.90118 s

method {:test} Test2() {
expect 25436 > 0 && 8858 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(25436, 8858);
}
method {:test} Test3() {
expect 17716 > 0 && 8858 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(17716, 8858);
}

// REPEAT 2 - TIME: 3.9699463 s

method {:test} Test4() {
expect 40876 > 0 && 20438 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(40876, 20438);
}
method {:test} Test5() {
expect 25437 > 0 && 8859 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(25437, 8859);
}

// REPEAT 3 - TIME: 5.1806126 s

method {:test} Test6() {
expect 40878 > 0 && 20439 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(40878, 20439);
}

// REPEAT 4 - TIME: 6.4041727 s

method {:test} Test8() {
expect 40880 > 0 && 20440 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(40880, 20440);
}
method {:test} Test9() {
expect 42117 > 0 && 20440 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(42117, 20440);
}

// REPEAT 5 - TIME: 7.399646 s

method {:test} Test10() {
expect 42118 > 0 && 20441 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(42118, 20441);
}
method {:test} Test11() {
expect 57556 > 0 && 28778 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(57556, 28778);
}

// REPEAT 6 - TIME: 8.3153064 s

method {:test} Test12() {
expect 65278 > 0 && 28779 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(65278, 28779);
}
method {:test} Test13() {
expect 66414 > 0 && 28779 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(66414, 28779);
}

// REPEAT 7 - TIME: 9.2211956 s

method {:test} Test14() {
expect 81854 > 0 && 40927 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(81854, 40927);
}
method {:test} Test15() {
expect 66415 > 0 && 28780 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(66415, 28780);
}

// REPEAT 8 - TIME: 10.363829 s

method {:test} Test16() {
expect 83093 > 0 && 40928 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(83093, 40928);
}
method {:test} Test17() {
expect 84294 > 0 && 40928 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(84294, 40928);
}

// REPEAT 9 - TIME: 11.5106401 s

method {:test} Test18() {
expect 99734 > 0 && 49867 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(99734, 49867);
}
method {:test} Test19() {
expect 84295 > 0 && 40929 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(84295, 40929);
}

// REPEAT 10 - TIME: 12.4707121 s
