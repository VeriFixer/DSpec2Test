// Clover_quotient.dfy

method {:testEntry} Quotient(x: nat, y: nat)
    returns (r: int, q: int)
  requires y != 0
  ensures q * y + r == x && 0 <= r < y && 0 <= q
{
  r := x;
  q := 0;
  while y >= r
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

// REPEAT 1 - TIME: 2.2466537 s

method {:test} Test1() {
expect 2 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(1, 2);
expect r1 * 2 + r0 == 1 && 0 <= r0 < 2 && 0 <= r1;
}

// REPEAT 2 - TIME: 3.0459423 s

method {:test} Test2() {
expect 3 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(2, 3);
expect r1 * 3 + r0 == 2 && 0 <= r0 < 3 && 0 <= r1;
}

// REPEAT 3 - TIME: 4.1578016 s

method {:test} Test3() {
expect 4 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(3, 4);
expect r1 * 4 + r0 == 3 && 0 <= r0 < 4 && 0 <= r1;
}

// REPEAT 4 - TIME: 4.9521314 s

method {:test} Test4() {
expect 5 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(4, 5);
expect r1 * 5 + r0 == 4 && 0 <= r0 < 5 && 0 <= r1;
}

// REPEAT 5 - TIME: 5.808516 s

method {:test} Test5() {
expect 6 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(5, 6);
expect r1 * 6 + r0 == 5 && 0 <= r0 < 6 && 0 <= r1;
}

// REPEAT 6 - TIME: 6.6236248 s

method {:test} Test6() {
expect 7 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(6, 7);
expect r1 * 7 + r0 == 6 && 0 <= r0 < 7 && 0 <= r1;
}

// REPEAT 7 - TIME: 7.5210657 s

method {:test} Test7() {
expect 8 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7, 8);
expect r1 * 8 + r0 == 7 && 0 <= r0 < 8 && 0 <= r1;
}

// REPEAT 8 - TIME: 8.3426265 s

method {:test} Test8() {
expect 9 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(8, 9);
expect r1 * 9 + r0 == 8 && 0 <= r0 < 9 && 0 <= r1;
}

// REPEAT 9 - TIME: 9.1001761 s

method {:test} Test9() {
expect 10 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(9, 10);
expect r1 * 10 + r0 == 9 && 0 <= r0 < 10 && 0 <= r1;
}

// REPEAT 10 - TIME: 9.8036668 s
