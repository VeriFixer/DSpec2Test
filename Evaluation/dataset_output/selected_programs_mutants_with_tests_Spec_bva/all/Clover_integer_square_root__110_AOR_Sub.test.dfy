// Clover_integer_square_root.dfy

method {:testEntry} SquareRoot(N: nat) returns (r: nat)
  ensures r * r <= N < (r + 1) * (r + 1)
{
  r := 0;
  while r + 1 - (r + 1) <= N
    invariant r * r <= N
  {
    r := r + 1;
  }
}


method {:test} Test0() {
var r0 := SquareRoot(0);
expect r0 * r0 <= 0 < (r0 + 1) * (r0 + 1);
}
method {:test} Test1() {
var r0 := SquareRoot(100);
expect r0 * r0 <= 100 < (r0 + 1) * (r0 + 1);
}
method {:test} Test3() {
var r0 := SquareRoot(10000);
expect r0 * r0 <= 10000 < (r0 + 1) * (r0 + 1);
}

// REPEAT 1 - TIME: 6.1331365 s

method {:test} Test6() {
var r0 := SquareRoot(10001);
expect r0 * r0 <= 10001 < (r0 + 1) * (r0 + 1);
}

// REPEAT 2 - TIME: 7.3020147 s

method {:test} Test7() {
var r0 := SquareRoot(10200);
expect r0 * r0 <= 10200 < (r0 + 1) * (r0 + 1);
}

// REPEAT 3 - TIME: 8.1983682 s

method {:test} Test8() {
var r0 := SquareRoot(10403);
expect r0 * r0 <= 10403 < (r0 + 1) * (r0 + 1);
}

// REPEAT 4 - TIME: 9.0746704 s

method {:test} Test9() {
var r0 := SquareRoot(10608);
expect r0 * r0 <= 10608 < (r0 + 1) * (r0 + 1);
}

// REPEAT 5 - TIME: 9.8765861 s

method {:test} Test10() {
var r0 := SquareRoot(10815);
expect r0 * r0 <= 10815 < (r0 + 1) * (r0 + 1);
}

// REPEAT 6 - TIME: 10.568989 s

method {:test} Test11() {
var r0 := SquareRoot(10816);
expect r0 * r0 <= 10816 < (r0 + 1) * (r0 + 1);
}

// REPEAT 7 - TIME: 11.2619208 s

method {:test} Test12() {
var r0 := SquareRoot(10817);
expect r0 * r0 <= 10817 < (r0 + 1) * (r0 + 1);
}

// REPEAT 8 - TIME: 12.0416745 s

method {:test} Test13() {
var r0 := SquareRoot(10818);
expect r0 * r0 <= 10818 < (r0 + 1) * (r0 + 1);
}

// REPEAT 9 - TIME: 12.8826203 s

method {:test} Test14() {
var r0 := SquareRoot(10819);
expect r0 * r0 <= 10819 < (r0 + 1) * (r0 + 1);
}

// REPEAT 10 - TIME: 13.6607667 s
