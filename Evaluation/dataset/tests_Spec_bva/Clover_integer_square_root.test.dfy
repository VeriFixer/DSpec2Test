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

// REPEAT 1 - TIME: 5.165088 s

method {:test} Test6() {
var r0 := SquareRoot(10001);
expect r0 * r0 <= 10001 < (r0 + 1) * (r0 + 1);
}

// REPEAT 2 - TIME: 6.1005344 s

method {:test} Test7() {
var r0 := SquareRoot(10200);
expect r0 * r0 <= 10200 < (r0 + 1) * (r0 + 1);
}

// REPEAT 3 - TIME: 6.8983132 s

method {:test} Test8() {
var r0 := SquareRoot(10403);
expect r0 * r0 <= 10403 < (r0 + 1) * (r0 + 1);
}

// REPEAT 4 - TIME: 7.6918125 s

method {:test} Test9() {
var r0 := SquareRoot(10608);
expect r0 * r0 <= 10608 < (r0 + 1) * (r0 + 1);
}

// REPEAT 5 - TIME: 8.4238337 s

method {:test} Test10() {
var r0 := SquareRoot(10815);
expect r0 * r0 <= 10815 < (r0 + 1) * (r0 + 1);
}

// REPEAT 6 - TIME: 9.1047985 s

method {:test} Test11() {
var r0 := SquareRoot(10816);
expect r0 * r0 <= 10816 < (r0 + 1) * (r0 + 1);
}

// REPEAT 7 - TIME: 9.7714153 s

method {:test} Test12() {
var r0 := SquareRoot(10817);
expect r0 * r0 <= 10817 < (r0 + 1) * (r0 + 1);
}

// REPEAT 8 - TIME: 10.384828 s

method {:test} Test13() {
var r0 := SquareRoot(10818);
expect r0 * r0 <= 10818 < (r0 + 1) * (r0 + 1);
}

// REPEAT 9 - TIME: 11.0455095 s

method {:test} Test14() {
var r0 := SquareRoot(10819);
expect r0 * r0 <= 10819 < (r0 + 1) * (r0 + 1);
}

// REPEAT 10 - TIME: 11.6398026 s
