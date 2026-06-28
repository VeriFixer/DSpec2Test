// Dafny-Exercises_tmp_tmpjm75muf__Session2Exercises_ExerciseSquare_root.dfy

method {:testEntry} mroot1(n: int) returns (r: int)
  requires n >= 0
  ensures r >= 0 && r * r <= n < (r + 1) * (r + 1)
{
  r := 0;
  while true
    invariant r >= 0 && r * r <= n
    decreases n - r * r
  {
    r := r + 1;
  }
}

method {:testEntry} mroot2(n: int) returns (r: int)
  requires n >= 0
  ensures r >= 0 && r * r <= n < (r + 1) * (r + 1)
{
  r := n;
  while n < r * r
    invariant 0 <= r <= n && n < (r + 1) * (r + 1)
    invariant r * r <= n ==> n < (r + 1) * (r + 1)
    decreases r
  {
    r := r - 1;
  }
}

method {:testEntry} mroot3(n: int) returns (r: int)
  requires n >= 0
  ensures r >= 0 && r * r <= n < (r + 1) * (r + 1)
{
  var y: int;
  var h: int;
  r := 0;
  y := n + 1;
  while y != r + 1
    invariant r >= 0 && r * r <= n < y * y && y >= r + 1
    decreases y - r
  {
    h := (r + y) / 2;
    if h * h <= n {
      r := h;
    } else {
      y := h;
    }
  }
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(0);
expect r0 >= 0 && r0 * r0 <= 0 < (r0 + 1) * (r0 + 1);
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(100);
expect r0 >= 0 && r0 * r0 <= 100 < (r0 + 1) * (r0 + 1);
}
method {:test} Test5() {
expect 10000 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(10000);
expect r0 >= 0 && r0 * r0 <= 10000 < (r0 + 1) * (r0 + 1);
}
method {:test} Test8() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(0);
expect r0 >= 0 && r0 * r0 <= 0 < (r0 + 1) * (r0 + 1);
}
method {:test} Test10() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(100);
expect r0 >= 0 && r0 * r0 <= 100 < (r0 + 1) * (r0 + 1);
}
method {:test} Test13() {
expect 10000 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(10000);
expect r0 >= 0 && r0 * r0 <= 10000 < (r0 + 1) * (r0 + 1);
}
method {:test} Test16() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(0);
expect r0 >= 0 && r0 * r0 <= 0 < (r0 + 1) * (r0 + 1);
}
method {:test} Test18() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(100);
expect r0 >= 0 && r0 * r0 <= 100 < (r0 + 1) * (r0 + 1);
}
method {:test} Test21() {
expect 10000 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(10000);
expect r0 >= 0 && r0 * r0 <= 10000 < (r0 + 1) * (r0 + 1);
}

// REPEAT 1 - TIME: 17.8960146 s

method {:test} Test24() {
expect 10001 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(10001);
expect r0 >= 0 && r0 * r0 <= 10001 < (r0 + 1) * (r0 + 1);
}
method {:test} Test25() {
expect 10001 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(10001);
expect r0 >= 0 && r0 * r0 <= 10001 < (r0 + 1) * (r0 + 1);
}
method {:test} Test26() {
expect 10001 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(10001);
expect r0 >= 0 && r0 * r0 <= 10001 < (r0 + 1) * (r0 + 1);
}

// REPEAT 2 - TIME: 19.9158007 s

method {:test} Test27() {
expect 10200 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(10200);
expect r0 >= 0 && r0 * r0 <= 10200 < (r0 + 1) * (r0 + 1);
}
method {:test} Test28() {
expect 10200 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(10200);
expect r0 >= 0 && r0 * r0 <= 10200 < (r0 + 1) * (r0 + 1);
}
method {:test} Test29() {
expect 10200 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(10200);
expect r0 >= 0 && r0 * r0 <= 10200 < (r0 + 1) * (r0 + 1);
}

// REPEAT 3 - TIME: 21.5898757 s

method {:test} Test30() {
expect 10403 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(10403);
expect r0 >= 0 && r0 * r0 <= 10403 < (r0 + 1) * (r0 + 1);
}
method {:test} Test31() {
expect 10403 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(10403);
expect r0 >= 0 && r0 * r0 <= 10403 < (r0 + 1) * (r0 + 1);
}
method {:test} Test32() {
expect 10403 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(10403);
expect r0 >= 0 && r0 * r0 <= 10403 < (r0 + 1) * (r0 + 1);
}

// REPEAT 4 - TIME: 23.307019 s

method {:test} Test33() {
expect 10404 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(10404);
expect r0 >= 0 && r0 * r0 <= 10404 < (r0 + 1) * (r0 + 1);
}
method {:test} Test34() {
expect 10404 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(10404);
expect r0 >= 0 && r0 * r0 <= 10404 < (r0 + 1) * (r0 + 1);
}
method {:test} Test35() {
expect 10404 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(10404);
expect r0 >= 0 && r0 * r0 <= 10404 < (r0 + 1) * (r0 + 1);
}

// REPEAT 5 - TIME: 25.1563177 s

method {:test} Test36() {
expect 10608 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(10608);
expect r0 >= 0 && r0 * r0 <= 10608 < (r0 + 1) * (r0 + 1);
}
method {:test} Test37() {
expect 10608 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(10608);
expect r0 >= 0 && r0 * r0 <= 10608 < (r0 + 1) * (r0 + 1);
}
method {:test} Test38() {
expect 10608 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(10608);
expect r0 >= 0 && r0 * r0 <= 10608 < (r0 + 1) * (r0 + 1);
}

// REPEAT 6 - TIME: 26.8680336 s

method {:test} Test39() {
expect 10815 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(10815);
expect r0 >= 0 && r0 * r0 <= 10815 < (r0 + 1) * (r0 + 1);
}
method {:test} Test40() {
expect 10815 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(10815);
expect r0 >= 0 && r0 * r0 <= 10815 < (r0 + 1) * (r0 + 1);
}
method {:test} Test41() {
expect 10815 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(10815);
expect r0 >= 0 && r0 * r0 <= 10815 < (r0 + 1) * (r0 + 1);
}

// REPEAT 7 - TIME: 28.7056654 s

method {:test} Test42() {
expect 10816 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(10816);
expect r0 >= 0 && r0 * r0 <= 10816 < (r0 + 1) * (r0 + 1);
}
method {:test} Test43() {
expect 10816 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(10816);
expect r0 >= 0 && r0 * r0 <= 10816 < (r0 + 1) * (r0 + 1);
}
method {:test} Test44() {
expect 10816 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(10816);
expect r0 >= 0 && r0 * r0 <= 10816 < (r0 + 1) * (r0 + 1);
}

// REPEAT 8 - TIME: 30.227719 s

method {:test} Test45() {
expect 10817 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(10817);
expect r0 >= 0 && r0 * r0 <= 10817 < (r0 + 1) * (r0 + 1);
}
method {:test} Test46() {
expect 10817 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(10817);
expect r0 >= 0 && r0 * r0 <= 10817 < (r0 + 1) * (r0 + 1);
}
method {:test} Test47() {
expect 10817 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(10817);
expect r0 >= 0 && r0 * r0 <= 10817 < (r0 + 1) * (r0 + 1);
}

// REPEAT 9 - TIME: 31.9297497 s

method {:test} Test48() {
expect 10818 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(10818);
expect r0 >= 0 && r0 * r0 <= 10818 < (r0 + 1) * (r0 + 1);
}
method {:test} Test49() {
expect 10818 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(10818);
expect r0 >= 0 && r0 * r0 <= 10818 < (r0 + 1) * (r0 + 1);
}
method {:test} Test50() {
expect 10818 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(10818);
expect r0 >= 0 && r0 * r0 <= 10818 < (r0 + 1) * (r0 + 1);
}

// REPEAT 10 - TIME: 33.706496 s
