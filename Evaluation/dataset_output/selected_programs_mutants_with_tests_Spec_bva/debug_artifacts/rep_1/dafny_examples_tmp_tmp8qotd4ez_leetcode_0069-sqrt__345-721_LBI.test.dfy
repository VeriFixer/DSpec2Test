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
    break;
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
