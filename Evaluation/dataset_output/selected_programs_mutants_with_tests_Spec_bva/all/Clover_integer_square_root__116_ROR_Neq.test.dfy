// Clover_integer_square_root.dfy

method {:testEntry} SquareRoot(N: nat) returns (r: nat)
  ensures r * r <= N < (r + 1) * (r + 1)
{
  r := 0;
  while (r + 1) * (r + 1) != N
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

// REPEAT 1 - TIME: 7.8440608 s

method {:test} Test6() {
var r0 := SquareRoot(10001);
expect r0 * r0 <= 10001 < (r0 + 1) * (r0 + 1);
}

// REPEAT 2 - TIME: 9.0216108 s

method {:test} Test7() {
var r0 := SquareRoot(10200);
expect r0 * r0 <= 10200 < (r0 + 1) * (r0 + 1);
}

// REPEAT 3 - TIME: 10.396431 s

method {:test} Test8() {
var r0 := SquareRoot(10403);
expect r0 * r0 <= 10403 < (r0 + 1) * (r0 + 1);
}

// REPEAT 4 - TIME: 11.5655171 s

method {:test} Test9() {
var r0 := SquareRoot(10608);
expect r0 * r0 <= 10608 < (r0 + 1) * (r0 + 1);
}

// REPEAT 5 - TIME: 12.9374332 s

method {:test} Test10() {
var r0 := SquareRoot(10815);
expect r0 * r0 <= 10815 < (r0 + 1) * (r0 + 1);
}

// REPEAT 6 - TIME: 13.9279615 s

method {:test} Test11() {
var r0 := SquareRoot(10816);
expect r0 * r0 <= 10816 < (r0 + 1) * (r0 + 1);
}

// REPEAT 7 - TIME: 15.1039853 s

method {:test} Test12() {
var r0 := SquareRoot(10817);
expect r0 * r0 <= 10817 < (r0 + 1) * (r0 + 1);
}

// REPEAT 8 - TIME: 16.419479 s

method {:test} Test13() {
var r0 := SquareRoot(10818);
expect r0 * r0 <= 10818 < (r0 + 1) * (r0 + 1);
}

// REPEAT 9 - TIME: 17.5818074 s

method {:test} Test14() {
var r0 := SquareRoot(10819);
expect r0 * r0 <= 10819 < (r0 + 1) * (r0 + 1);
}

// REPEAT 10 - TIME: 18.410701 s
