// Clover_integer_square_root.dfy

method {:testEntry} SquareRoot(N: nat) returns (r: nat)
  ensures r * r <= N < (r + 1) * (r + 1)
{
  r := 0;
  while (r + 1) * (r + 1) >= N
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

// REPEAT 1 - TIME: 2.361069 s

method {:test} Test1() {
var r0 := SquareRoot(3);
expect r0 * r0 <= 3 < (r0 + 1) * (r0 + 1);
}

// REPEAT 2 - TIME: 3.2210813 s

method {:test} Test2() {
var r0 := SquareRoot(4);
expect r0 * r0 <= 4 < (r0 + 1) * (r0 + 1);
}

// REPEAT 3 - TIME: 4.1720009 s

method {:test} Test3() {
var r0 := SquareRoot(5);
expect r0 * r0 <= 5 < (r0 + 1) * (r0 + 1);
}

// REPEAT 4 - TIME: 5.2337023 s

method {:test} Test4() {
var r0 := SquareRoot(15);
expect r0 * r0 <= 15 < (r0 + 1) * (r0 + 1);
}

// REPEAT 5 - TIME: 6.1035987 s

method {:test} Test5() {
var r0 := SquareRoot(16);
expect r0 * r0 <= 16 < (r0 + 1) * (r0 + 1);
}

// REPEAT 6 - TIME: 6.9293707 s

method {:test} Test6() {
var r0 := SquareRoot(24);
expect r0 * r0 <= 24 < (r0 + 1) * (r0 + 1);
}

// REPEAT 7 - TIME: 7.542273 s

method {:test} Test7() {
var r0 := SquareRoot(25);
expect r0 * r0 <= 25 < (r0 + 1) * (r0 + 1);
}

// REPEAT 8 - TIME: 8.2551152 s

method {:test} Test8() {
var r0 := SquareRoot(26);
expect r0 * r0 <= 26 < (r0 + 1) * (r0 + 1);
}

// REPEAT 9 - TIME: 9.1158786 s

method {:test} Test9() {
var r0 := SquareRoot(35);
expect r0 * r0 <= 35 < (r0 + 1) * (r0 + 1);
}

// REPEAT 10 - TIME: 9.715447 s
