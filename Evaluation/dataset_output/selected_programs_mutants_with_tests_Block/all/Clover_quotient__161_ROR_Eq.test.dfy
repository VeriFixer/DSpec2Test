// Clover_quotient.dfy

method {:testEntry} Quotient(x: nat, y: nat)
    returns (r: int, q: int)
  requires y != 0
  ensures q * y + r == x && 0 <= r < y && 0 <= q
{
  r := x;
  q := 0;
  while y == r
    invariant q * y + r == x && r >= 0
    decreases r
  {
    r := r - y;
    q := q + 1;
  }
}


method {:test} Test0() {
expect 1 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(1, 1);
expect r1 * 1 + r0 == 1 && 0 <= r0 < 1 && 0 <= r1;
}

// REPEAT 1 - TIME: 1.9178537 s

method {:test} Test1() {
expect 7721 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7721, 7721);
expect r1 * 7721 + r0 == 7721 && 0 <= r0 < 7721 && 0 <= r1;
}

// REPEAT 2 - TIME: 2.5538515 s

method {:test} Test2() {
expect 7722 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7722, 7722);
expect r1 * 7722 + r0 == 7722 && 0 <= r0 < 7722 && 0 <= r1;
}

// REPEAT 3 - TIME: 3.2909211 s

method {:test} Test3() {
expect 7723 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7723, 7723);
expect r1 * 7723 + r0 == 7723 && 0 <= r0 < 7723 && 0 <= r1;
}

// REPEAT 4 - TIME: 3.9411918 s

method {:test} Test4() {
expect 7724 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7724, 7724);
expect r1 * 7724 + r0 == 7724 && 0 <= r0 < 7724 && 0 <= r1;
}

// REPEAT 5 - TIME: 4.6162451 s

method {:test} Test5() {
expect 7725 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7725, 7725);
expect r1 * 7725 + r0 == 7725 && 0 <= r0 < 7725 && 0 <= r1;
}

// REPEAT 6 - TIME: 5.2617109 s

method {:test} Test6() {
expect 7726 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7726, 7726);
expect r1 * 7726 + r0 == 7726 && 0 <= r0 < 7726 && 0 <= r1;
}

// REPEAT 7 - TIME: 5.9418844 s

method {:test} Test7() {
expect 7727 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7727, 7727);
expect r1 * 7727 + r0 == 7727 && 0 <= r0 < 7727 && 0 <= r1;
}

// REPEAT 8 - TIME: 6.6576997 s

method {:test} Test8() {
expect 7728 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7728, 7728);
expect r1 * 7728 + r0 == 7728 && 0 <= r0 < 7728 && 0 <= r1;
}

// REPEAT 9 - TIME: 7.3353879 s

method {:test} Test9() {
expect 7729 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7729, 7729);
expect r1 * 7729 + r0 == 7729 && 0 <= r0 < 7729 && 0 <= r1;
}

// REPEAT 10 - TIME: 7.8468117 s
