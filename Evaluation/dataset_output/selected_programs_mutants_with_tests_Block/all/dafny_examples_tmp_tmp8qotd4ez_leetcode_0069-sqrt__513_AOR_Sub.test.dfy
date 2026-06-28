// dafny_examples_tmp_tmp8qotd4ez_leetcode_0069-sqrt.dfy

predicate sqrt(x: int, r: int)
{
  r * r <= x &&
  (r + 1) * (r + 1) > x
}

lemma uniqueSqrt(x: int, r1: int, r2: int)
  requires x >= 0 && r1 >= 0 && r2 >= 0
  ensures sqrt(x, r1) && sqrt(x, r2) ==> r1 == r2
{
}

method {:testEntry} mySqrt(x: int) returns (res: int)
  requires 0 <= x
  ensures sqrt(x, res)
{
  var l, r := 0, x;
  while l <= r
    invariant l >= 0
    invariant r >= 0
    invariant l * l <= x
    invariant (r + 1) * (r + 1) > x
    decreases r - l
  {
    var mid := l + r - 2;
    if mid * mid <= x && (mid + 1) * (mid + 1) > x {
      return mid;
    } else if mid * mid <= x {
      l := mid + 1;
    } else {
      r := mid - 1;
    }
  }
}


method {:test} Test0() {
expect 0 <= 6, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(6);
expect sqrt(6, r0);
}
method {:test} Test1() {
expect 0 <= 9, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(9);
expect sqrt(9, r0);
}
method {:test} Test2() {
expect 0 <= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(0);
expect sqrt(0, r0);
}

// REPEAT 1 - TIME: 4.1095748 s

method {:test} Test3() {
expect 0 <= 10, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(10);
expect sqrt(10, r0);
}
method {:test} Test5() {
expect 0 <= 15, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(15);
expect sqrt(15, r0);
}

// REPEAT 2 - TIME: 6.0450763 s

method {:test} Test6() {
expect 0 <= 16, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(16);
expect sqrt(16, r0);
}
method {:test} Test7() {
expect 0 <= 275625, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(275625);
expect sqrt(275625, r0);
}
method {:test} Test8() {
expect 0 <= 25, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(25);
expect sqrt(25, r0);
}

// REPEAT 3 - TIME: 13.966031 s

method {:test} Test9() {
expect 0 <= 276675, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(276675);
expect sqrt(276675, r0);
}
method {:test} Test10() {
expect 0 <= 277729, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(277729);
expect sqrt(277729, r0);
}
method {:test} Test11() {
expect 0 <= 277728, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(277728);
expect sqrt(277728, r0);
}

// REPEAT 4 - TIME: 35.4461671 s

method {:test} Test12() {
expect 0 <= 277730, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(277730);
expect sqrt(277730, r0);
}
method {:test} Test13() {
expect 0 <= 368448, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(368448);
expect sqrt(368448, r0);
}

// REPEAT 5 - TIME: 83.6579459 s

method {:test} Test14() {
expect 0 <= 369663, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(369663);
expect sqrt(369663, r0);
}
method {:test} Test15() {
expect 0 <= 370881, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(370881);
expect sqrt(370881, r0);
}
method {:test} Test16() {
expect 0 <= 370880, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(370880);
expect sqrt(370880, r0);
}

// REPEAT 6 - TIME: 100.1348317 s

method {:test} Test17() {
expect 0 <= 372099, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(372099);
expect sqrt(372099, r0);
}
method {:test} Test18() {
expect 0 <= 373321, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(373321);
expect sqrt(373321, r0);
}
method {:test} Test19() {
expect 0 <= 372100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(372100);
expect sqrt(372100, r0);
}

// REPEAT 7 - TIME: 110.1366087 s

method {:test} Test20() {
expect 0 <= 374543, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(374543);
expect sqrt(374543, r0);
}
method {:test} Test21() {
expect 0 <= 1236543, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(1236543);
expect sqrt(1236543, r0);
}

// REPEAT 8 - TIME: 157.0634007 s

method {:test} Test23() {
expect 0 <= 1238768, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(1238768);
expect sqrt(1238768, r0);
}
method {:test} Test24() {
expect 0 <= 1240996, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(1240996);
expect sqrt(1240996, r0);
}

// REPEAT 9 - TIME: 178.1917467 s

method {:test} Test26() {
expect 0 <= 1243224, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(1243224);
expect sqrt(1243224, r0);
}
method {:test} Test27() {
expect 0 <= 2627640, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(2627640);
expect sqrt(2627640, r0);
}

// REPEAT 10 - TIME: 235.8145238 s
