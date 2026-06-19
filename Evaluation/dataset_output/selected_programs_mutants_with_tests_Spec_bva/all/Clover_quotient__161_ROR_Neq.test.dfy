// Clover_quotient.dfy

method {:testEntry} Quotient(x: nat, y: nat)
    returns (r: int, q: int)
  requires y != 0
  ensures q * y + r == x && 0 <= r < y && 0 <= q
{
  r := x;
  q := 0;
  while y != r
    invariant q * y + r == x && r >= 0
    decreases r
  {
    r := r - y;
    q := q + 1;
  }
}


method {:test} Test0() {
expect 1 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(0, 1);
expect r1 * 1 + r0 == 0 && 0 <= r0 < 1 && 0 <= r1;
}
method {:test} Test1() {
expect 1 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(100, 1);
expect r1 * 1 + r0 == 100 && 0 <= r0 < 1 && 0 <= r1;
}
method {:test} Test2() {
expect 100 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(3800, 100);
expect r1 * 100 + r0 == 3800 && 0 <= r0 < 100 && 0 <= r1;
}
method {:test} Test5() {
expect 101 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(246237, 101);
expect r1 * 101 + r0 == 246237 && 0 <= r0 < 101 && 0 <= r1;
}

// REPEAT 1 - TIME: 8.3191466 s

method {:test} Test11() {
expect 102 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(246330, 102);
expect r1 * 102 + r0 == 246330 && 0 <= r0 < 102 && 0 <= r1;
}

// REPEAT 2 - TIME: 9.182552 s

method {:test} Test12() {
expect 246332 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(246331, 246332);
expect r1 * 246332 + r0 == 246331 && 0 <= r0 < 246332 && 0 <= r1;
}

// REPEAT 3 - TIME: 9.9698081 s

method {:test} Test13() {
expect 246333 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(246332, 246333);
expect r1 * 246333 + r0 == 246332 && 0 <= r0 < 246333 && 0 <= r1;
}

// REPEAT 4 - TIME: 10.7750925 s

method {:test} Test14() {
expect 246334 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(246333, 246334);
expect r1 * 246334 + r0 == 246333 && 0 <= r0 < 246334 && 0 <= r1;
}

// REPEAT 5 - TIME: 11.6206277 s

method {:test} Test15() {
expect 246335 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(246334, 246335);
expect r1 * 246335 + r0 == 246334 && 0 <= r0 < 246335 && 0 <= r1;
}

// REPEAT 6 - TIME: 12.3899722 s

method {:test} Test16() {
expect 246336 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(246335, 246336);
expect r1 * 246336 + r0 == 246335 && 0 <= r0 < 246336 && 0 <= r1;
}

// REPEAT 7 - TIME: 13.1550008 s

method {:test} Test17() {
expect 246337 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(246336, 246337);
expect r1 * 246337 + r0 == 246336 && 0 <= r0 < 246337 && 0 <= r1;
}

// REPEAT 8 - TIME: 13.8483143 s

method {:test} Test18() {
expect 246338 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(246337, 246338);
expect r1 * 246338 + r0 == 246337 && 0 <= r0 < 246338 && 0 <= r1;
}

// REPEAT 9 - TIME: 14.3978215 s

method {:test} Test19() {
expect 246339 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(246338, 246339);
expect r1 * 246339 + r0 == 246338 && 0 <= r0 < 246339 && 0 <= r1;
}

// REPEAT 10 - TIME: 14.9813229 s
