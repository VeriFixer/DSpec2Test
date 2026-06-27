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

// REPEAT 1 - TIME: 4.8956418 s

method {:test} Test3() {
expect 0 <= 10, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(10);
expect sqrt(10, r0);
}
method {:test} Test5() {
expect 0 <= 326042, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(326042);
expect sqrt(326042, r0);
}

// REPEAT 2 - TIME: 19.3678097 s

method {:test} Test6() {
expect 0 <= 327183, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(327183);
expect sqrt(327183, r0);
}
method {:test} Test7() {
expect 0 <= 326043, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(326043);
expect sqrt(326043, r0);
}
method {:test} Test8() {
expect 0 <= 327184, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(327184);
expect sqrt(327184, r0);
}

// REPEAT 3 - TIME: 48.4003341 s

method {:test} Test9() {
expect 0 <= 327185, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(327185);
expect sqrt(327185, r0);
}
method {:test} Test10() {
expect 0 <= 425103, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(425103);
expect sqrt(425103, r0);
}
method {:test} Test11() {
expect 0 <= 328329, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(328329);
expect sqrt(328329, r0);
}

// REPEAT 4 - TIME: 70.4860689 s

method {:test} Test12() {
expect 0 <= 426408, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(426408);
expect sqrt(426408, r0);
}

// REPEAT 5 - TIME: 96.2517533 s

method {:test} Test15() {
expect 0 <= 426409, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(426409);
expect sqrt(426409, r0);
}
method {:test} Test16() {
expect 0 <= 1432808, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(1432808);
expect sqrt(1432808, r0);
}
method {:test} Test17() {
expect 0 <= 429024, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(429024);
expect sqrt(429024, r0);
}

// REPEAT 6 - TIME: 106.9060025 s

method {:test} Test18() {
expect 0 <= 1432809, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(1432809);
expect sqrt(1432809, r0);
}
method {:test} Test19() {
expect 0 <= 5354596, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(5354596);
expect sqrt(5354596, r0);
}
method {:test} Test20() {
expect 0 <= 1435204, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(1435204);
expect sqrt(1435204, r0);
}

// REPEAT 7 - TIME: 128.6707549 s

method {:test} Test21() {
expect 0 <= 5359224, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(5359224);
expect sqrt(5359224, r0);
}
method {:test} Test22() {
expect 0 <= 21307455, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(21307455);
expect sqrt(21307455, r0);
}
method {:test} Test23() {
expect 0 <= 5359226, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(5359226);
expect sqrt(5359226, r0);
}

// REPEAT 8 - TIME: 163.455662 s

method {:test} Test24() {
expect 0 <= 21316688, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(21316688);
expect sqrt(21316688, r0);
}
method {:test} Test25() {
expect 0 <= 21325924, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(21325924);
expect sqrt(21325924, r0);
}
method {:test} Test26() {
expect 0 <= 21307456, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(21307456);
expect sqrt(21307456, r0);
}

// REPEAT 9 - TIME: 223.924316 s

method {:test} Test27() {
expect 0 <= 21335160, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(21335160);
expect sqrt(21335160, r0);
}
method {:test} Test28() {
expect 0 <= 21344400, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mySqrt(21344400);
expect sqrt(21344400, r0);
}

// REPEAT 10 - TIME: 296.0794724 s
