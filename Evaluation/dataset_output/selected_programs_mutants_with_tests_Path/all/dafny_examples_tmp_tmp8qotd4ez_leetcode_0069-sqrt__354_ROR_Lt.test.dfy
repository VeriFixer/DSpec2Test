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
  while l < r
    invariant l >= 0
    invariant r >= 0
    invariant l * l <= x
    invariant (r + 1) * (r + 1) > x
    decreases r - l
  {
    var mid := (l + r) / 2;
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
expect 0 <= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(0);
expect sqrt(0, r0);
}

// REPEAT 1 - TIME: 8.2737468 s

method {:test} Test2() {
expect 0 <= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(1);
expect sqrt(1, r0);
}
method {:test} Test3() {
expect 0 <= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(2);
expect sqrt(2, r0);
}

// REPEAT 2 - TIME: 14.0380055 s

method {:test} Test4() {
expect 0 <= 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(3);
expect sqrt(3, r0);
}

// REPEAT 3 - TIME: 19.6195117 s

method {:test} Test6() {
expect 0 <= 8, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(8);
expect sqrt(8, r0);
}
method {:test} Test7() {
expect 0 <= 4, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(4);
expect sqrt(4, r0);
}

// REPEAT 4 - TIME: 25.7586025 s

method {:test} Test8() {
expect 0 <= 15, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(15);
expect sqrt(15, r0);
}

// REPEAT 5 - TIME: 32.1744339 s

method {:test} Test10() {
expect 0 <= 24, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(24);
expect sqrt(24, r0);
}

// REPEAT 6 - TIME: 39.4278749 s

method {:test} Test12() {
expect 0 <= 25, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(25);
expect sqrt(25, r0);
}

// REPEAT 7 - TIME: 46.7288744 s

method {:test} Test14() {
expect 0 <= 35, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(35);
expect sqrt(35, r0);
}

// REPEAT 8 - TIME: 53.470402 s

method {:test} Test16() {
expect 0 <= 36, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(36);
expect sqrt(36, r0);
}

// REPEAT 9 - TIME: 59.9494512 s

method {:test} Test18() {
expect 0 <= 64, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(64);
expect sqrt(64, r0);
}

// REPEAT 10 - TIME: 68.1008467 s
