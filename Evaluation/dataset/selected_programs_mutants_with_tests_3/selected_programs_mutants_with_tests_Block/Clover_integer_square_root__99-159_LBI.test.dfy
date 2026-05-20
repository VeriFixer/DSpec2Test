// Clover_integer_square_root.dfy

method {:testEntry} SquareRoot(N: nat) returns (r: nat)
  ensures r * r <= N < (r + 1) * (r + 1)
{
  r := 0;
  while (r + 1) * (r + 1) <= N
    invariant r * r <= N
  {
    break;
    r := r + 1;
  }
}

method {:test} Test0() {
var r0 := SquareRoot(1);
expect r0 * r0 <= 1 < (r0 + 1) * (r0 + 1);
}
method {:test} Test1() {
var r0 := SquareRoot(2);
expect r0 * r0 <= 2 < (r0 + 1) * (r0 + 1);
}
method {:test} Test2() {
var r0 := SquareRoot(3);
expect r0 * r0 <= 3 < (r0 + 1) * (r0 + 1);
}
