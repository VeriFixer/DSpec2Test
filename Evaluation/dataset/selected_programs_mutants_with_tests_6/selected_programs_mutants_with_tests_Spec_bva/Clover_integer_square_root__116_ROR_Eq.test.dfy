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
method {:test} Test1() {
var r0 := SquareRoot(100);
expect r0 * r0 <= 100 < (r0 + 1) * (r0 + 1);
}
method {:test} Test3() {
var r0 := SquareRoot(10000);
expect r0 * r0 <= 10000 < (r0 + 1) * (r0 + 1);
}
method {:test} Test6() {
var r0 := SquareRoot(10001);
expect r0 * r0 <= 10001 < (r0 + 1) * (r0 + 1);
}
method {:test} Test7() {
var r0 := SquareRoot(10200);
expect r0 * r0 <= 10200 < (r0 + 1) * (r0 + 1);
}
method {:test} Test8() {
var r0 := SquareRoot(10403);
expect r0 * r0 <= 10403 < (r0 + 1) * (r0 + 1);
}
method {:test} Test9() {
var r0 := SquareRoot(10608);
expect r0 * r0 <= 10608 < (r0 + 1) * (r0 + 1);
}
method {:test} Test10() {
var r0 := SquareRoot(10815);
expect r0 * r0 <= 10815 < (r0 + 1) * (r0 + 1);
}
