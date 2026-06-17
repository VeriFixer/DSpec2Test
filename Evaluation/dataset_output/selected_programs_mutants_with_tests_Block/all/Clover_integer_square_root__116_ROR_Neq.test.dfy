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
var r0 := SquareRoot(1);
expect r0 * r0 <= 1 < (r0 + 1) * (r0 + 1);
}

// REPEAT 1 - TIME: 2.0362544 s

method {:test} Test1() {
var r0 := SquareRoot(2);
expect r0 * r0 <= 2 < (r0 + 1) * (r0 + 1);
}

// REPEAT 2 - TIME: 2.5966346 s

method {:test} Test2() {
var r0 := SquareRoot(3);
expect r0 * r0 <= 3 < (r0 + 1) * (r0 + 1);
}

// REPEAT 3 - TIME: 3.2461478 s

method {:test} Test3() {
var r0 := SquareRoot(4);
expect r0 * r0 <= 4 < (r0 + 1) * (r0 + 1);
}

// REPEAT 4 - TIME: 3.9625203 s

method {:test} Test4() {
var r0 := SquareRoot(5);
expect r0 * r0 <= 5 < (r0 + 1) * (r0 + 1);
}

// REPEAT 5 - TIME: 4.6237859 s

method {:test} Test5() {
var r0 := SquareRoot(6);
expect r0 * r0 <= 6 < (r0 + 1) * (r0 + 1);
}

// REPEAT 6 - TIME: 5.2750816 s

method {:test} Test6() {
var r0 := SquareRoot(7);
expect r0 * r0 <= 7 < (r0 + 1) * (r0 + 1);
}

// REPEAT 7 - TIME: 5.833228 s

method {:test} Test7() {
var r0 := SquareRoot(8);
expect r0 * r0 <= 8 < (r0 + 1) * (r0 + 1);
}

// REPEAT 8 - TIME: 6.5128131 s

method {:test} Test8() {
var r0 := SquareRoot(9);
expect r0 * r0 <= 9 < (r0 + 1) * (r0 + 1);
}

// REPEAT 9 - TIME: 7.1979389 s

method {:test} Test9() {
var r0 := SquareRoot(10);
expect r0 * r0 <= 10 < (r0 + 1) * (r0 + 1);
}

// REPEAT 10 - TIME: 7.9619733 s
