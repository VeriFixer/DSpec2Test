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
    var mid := l + r + 2;
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
expect 0 <= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(2);
expect sqrt(2, r0);
}
method {:test} Test1() {
expect 0 <= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(0);
expect sqrt(0, r0);
}
method {:test} Test2() {
expect 0 <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(100);
expect sqrt(100, r0);
}
method {:test} Test4() {
expect 0 <= 10000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(10000);
expect sqrt(10000, r0);
}

// REPEAT 1 - TIME: 31.7453683 s

method {:test} Test7() {
expect 0 <= 10001, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(10001);
expect sqrt(10001, r0);
}

// REPEAT 2 - TIME: 35.4040807 s

method {:test} Test8() {
expect 0 <= 10002, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(10002);
expect sqrt(10002, r0);
}

// REPEAT 3 - TIME: 39.1504522 s

method {:test} Test9() {
expect 0 <= 10003, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(10003);
expect sqrt(10003, r0);
}

// REPEAT 4 - TIME: 42.6157308 s

method {:test} Test10() {
expect 0 <= 10004, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(10004);
expect sqrt(10004, r0);
}

// REPEAT 5 - TIME: 45.8955592 s

method {:test} Test11() {
expect 0 <= 10200, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(10200);
expect sqrt(10200, r0);
}

// REPEAT 6 - TIME: 49.3660455 s

method {:test} Test12() {
expect 0 <= 10403, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(10403);
expect sqrt(10403, r0);
}

// REPEAT 7 - TIME: 52.6091352 s

method {:test} Test13() {
expect 0 <= 10404, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(10404);
expect sqrt(10404, r0);
}

// REPEAT 8 - TIME: 55.6500718 s

method {:test} Test14() {
expect 0 <= 10405, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(10405);
expect sqrt(10405, r0);
}

// REPEAT 9 - TIME: 59.0314892 s

method {:test} Test15() {
expect 0 <= 10406, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(10406);
expect sqrt(10406, r0);
}

// REPEAT 10 - TIME: 62.1224677 s
