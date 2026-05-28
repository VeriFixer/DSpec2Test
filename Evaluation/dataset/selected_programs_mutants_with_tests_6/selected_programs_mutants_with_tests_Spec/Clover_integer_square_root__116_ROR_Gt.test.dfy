// Clover_integer_square_root.dfy

method {:testEntry} SquareRoot(N: nat) returns (r: nat)
  ensures r * r <= N < (r + 1) * (r + 1)
{
  r := 0;
  while (r + 1) * (r + 1) > N
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
var r0 := SquareRoot(3);
expect r0 * r0 <= 3 < (r0 + 1) * (r0 + 1);
}
method {:test} Test2() {
var r0 := SquareRoot(4);
expect r0 * r0 <= 4 < (r0 + 1) * (r0 + 1);
}
method {:test} Test3() {
var r0 := SquareRoot(5);
expect r0 * r0 <= 5 < (r0 + 1) * (r0 + 1);
}
method {:test} Test4() {
var r0 := SquareRoot(15);
expect r0 * r0 <= 15 < (r0 + 1) * (r0 + 1);
}
method {:test} Test5() {
var r0 := SquareRoot(16);
expect r0 * r0 <= 16 < (r0 + 1) * (r0 + 1);
}
