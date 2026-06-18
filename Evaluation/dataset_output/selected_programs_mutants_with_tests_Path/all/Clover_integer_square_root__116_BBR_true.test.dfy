// Clover_integer_square_root.dfy

method {:testEntry} SquareRoot(N: nat) returns (r: nat)
  ensures r * r <= N < (r + 1) * (r + 1)
{
  r := 0;
  while true
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

// REPEAT 1 - TIME: 2.5724041 s

method {:test} Test1() {
var r0 := SquareRoot(1);
expect r0 * r0 <= 1 < (r0 + 1) * (r0 + 1);
}

// REPEAT 2 - TIME: 4.3684905 s

method {:test} Test2() {
var r0 := SquareRoot(3);
expect r0 * r0 <= 3 < (r0 + 1) * (r0 + 1);
}

// REPEAT 3 - TIME: 6.0831558 s

method {:test} Test3() {
var r0 := SquareRoot(4);
expect r0 * r0 <= 4 < (r0 + 1) * (r0 + 1);
}

// REPEAT 4 - TIME: 7.6161849 s

method {:test} Test4() {
var r0 := SquareRoot(5);
expect r0 * r0 <= 5 < (r0 + 1) * (r0 + 1);
}

// REPEAT 5 - TIME: 8.9005648 s

method {:test} Test5() {
var r0 := SquareRoot(6);
expect r0 * r0 <= 6 < (r0 + 1) * (r0 + 1);
}

// REPEAT 6 - TIME: 10.3263278 s

method {:test} Test6() {
var r0 := SquareRoot(7);
expect r0 * r0 <= 7 < (r0 + 1) * (r0 + 1);
}

// REPEAT 7 - TIME: 11.8007949 s

method {:test} Test7() {
var r0 := SquareRoot(8);
expect r0 * r0 <= 8 < (r0 + 1) * (r0 + 1);
}

// REPEAT 8 - TIME: 13.2601374 s

method {:test} Test8() {
var r0 := SquareRoot(9);
expect r0 * r0 <= 9 < (r0 + 1) * (r0 + 1);
}

// REPEAT 9 - TIME: 14.6434777 s

method {:test} Test9() {
var r0 := SquareRoot(10);
expect r0 * r0 <= 10 < (r0 + 1) * (r0 + 1);
}

// REPEAT 10 - TIME: 16.0605587 s
