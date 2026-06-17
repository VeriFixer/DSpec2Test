// Clover_integer_square_root.dfy

method {:testEntry} SquareRoot(N: nat) returns (r: nat)
  ensures r * r <= N < (r + 1) * (r + 1)
{
  r := 0;
  while (r + 1) * (r + 1) < N
    invariant r * r <= N
  {
    r := r + 1;
  }
}


method {:testEntry} SquareRoot(N:nat) returns (r:nat)
  ensures r*r <= N < (r+1)*(r+1)
{
  r:=0;
  while (r+1)*(r+1)<=N
    invariant r*r<=N
  {
    r:=r+1;
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

// REPEAT 1 - TIME: 4.9319852 s

method {:test} Test6() {
var r0 := SquareRoot(10001);
expect r0 * r0 <= 10001 < (r0 + 1) * (r0 + 1);
}

// REPEAT 2 - TIME: 5.808098 s

method {:test} Test7() {
var r0 := SquareRoot(10200);
expect r0 * r0 <= 10200 < (r0 + 1) * (r0 + 1);
}

// REPEAT 3 - TIME: 6.7172197 s

method {:test} Test8() {
var r0 := SquareRoot(10403);
expect r0 * r0 <= 10403 < (r0 + 1) * (r0 + 1);
}

// REPEAT 4 - TIME: 7.5147229 s

method {:test} Test9() {
var r0 := SquareRoot(10608);
expect r0 * r0 <= 10608 < (r0 + 1) * (r0 + 1);
}

// REPEAT 5 - TIME: 8.2691053 s

method {:test} Test10() {
var r0 := SquareRoot(10815);
expect r0 * r0 <= 10815 < (r0 + 1) * (r0 + 1);
}

// REPEAT 6 - TIME: 9.1053009 s

method {:test} Test11() {
var r0 := SquareRoot(10816);
expect r0 * r0 <= 10816 < (r0 + 1) * (r0 + 1);
}

// REPEAT 7 - TIME: 9.9037713 s

method {:test} Test12() {
var r0 := SquareRoot(10817);
expect r0 * r0 <= 10817 < (r0 + 1) * (r0 + 1);
}

// REPEAT 8 - TIME: 10.61334 s

method {:test} Test13() {
var r0 := SquareRoot(10818);
expect r0 * r0 <= 10818 < (r0 + 1) * (r0 + 1);
}

// REPEAT 9 - TIME: 11.2499619 s

method {:test} Test14() {
var r0 := SquareRoot(10819);
expect r0 * r0 <= 10819 < (r0 + 1) * (r0 + 1);
}

// REPEAT 10 - TIME: 12.167593 s
