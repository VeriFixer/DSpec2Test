// Clover_integer_square_root.dfy

method {:testEntry} SquareRoot(N: nat) returns (r: nat)
  ensures r * r <= N < (r + 1) * (r + 1)
{
  r := 0;
  while (r + 1) * (r + 1) == N
    invariant r * r <= N
  {
    r := r + 1;
  }
}


method {:test} Test0() {
var r0 := SquareRoot(0);
expect r0 * r0 <= 0 < (r0 + 1) * (r0 + 1);
}

// REPEAT 1 - TIME: 2.4909032 s

method {:test} Test1() {
var r0 := SquareRoot(3);
expect r0 * r0 <= 3 < (r0 + 1) * (r0 + 1);
}

// REPEAT 2 - TIME: 3.2828857 s

method {:test} Test2() {
var r0 := SquareRoot(4);
expect r0 * r0 <= 4 < (r0 + 1) * (r0 + 1);
}

// REPEAT 3 - TIME: 4.0565097 s

method {:test} Test3() {
var r0 := SquareRoot(5);
expect r0 * r0 <= 5 < (r0 + 1) * (r0 + 1);
}

// REPEAT 4 - TIME: 5.1885614 s

method {:test} Test4() {
var r0 := SquareRoot(15);
expect r0 * r0 <= 15 < (r0 + 1) * (r0 + 1);
}

// REPEAT 5 - TIME: 5.9273891 s

method {:test} Test5() {
var r0 := SquareRoot(16);
expect r0 * r0 <= 16 < (r0 + 1) * (r0 + 1);
}

// REPEAT 6 - TIME: 6.9136672 s

method {:test} Test6() {
var r0 := SquareRoot(24);
expect r0 * r0 <= 24 < (r0 + 1) * (r0 + 1);
}

// REPEAT 7 - TIME: 7.683484 s

method {:test} Test7() {
var r0 := SquareRoot(25);
expect r0 * r0 <= 25 < (r0 + 1) * (r0 + 1);
}

// REPEAT 8 - TIME: 8.4091999 s

method {:test} Test8() {
var r0 := SquareRoot(26);
expect r0 * r0 <= 26 < (r0 + 1) * (r0 + 1);
}

// REPEAT 9 - TIME: 8.9270597 s

method {:test} Test9() {
var r0 := SquareRoot(35);
expect r0 * r0 <= 35 < (r0 + 1) * (r0 + 1);
}

// REPEAT 10 - TIME: 9.4980942 s
