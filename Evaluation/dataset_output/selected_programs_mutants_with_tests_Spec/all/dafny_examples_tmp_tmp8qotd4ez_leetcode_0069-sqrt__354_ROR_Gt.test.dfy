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
  while l > r
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
expect 0 <= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(2);
expect sqrt(2, r0);
}

// REPEAT 1 - TIME: 5.8300226 s

method {:test} Test1() {
expect 0 <= 4, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(4);
expect sqrt(4, r0);
}

// REPEAT 2 - TIME: 9.3069799 s

method {:test} Test2() {
expect 0 <= 9, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(9);
expect sqrt(9, r0);
}

// REPEAT 3 - TIME: 12.0017736 s

method {:test} Test3() {
expect 0 <= 15, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(15);
expect sqrt(15, r0);
}

// REPEAT 4 - TIME: 14.9289895 s

method {:test} Test4() {
expect 0 <= 16, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(16);
expect sqrt(16, r0);
}

// REPEAT 5 - TIME: 17.8226565 s

method {:test} Test5() {
expect 0 <= 24, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(24);
expect sqrt(24, r0);
}

// REPEAT 6 - TIME: 20.2815266 s

method {:test} Test6() {
expect 0 <= 25, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(25);
expect sqrt(25, r0);
}

// REPEAT 7 - TIME: 22.7627335 s

method {:test} Test7() {
expect 0 <= 35, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(35);
expect sqrt(35, r0);
}

// REPEAT 8 - TIME: 25.7957256 s

method {:test} Test8() {
expect 0 <= 48, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(48);
expect sqrt(48, r0);
}

// REPEAT 9 - TIME: 28.437789 s

method {:test} Test9() {
expect 0 <= 63, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(63);
expect sqrt(63, r0);
}

// REPEAT 10 - TIME: 31.0239535 s
