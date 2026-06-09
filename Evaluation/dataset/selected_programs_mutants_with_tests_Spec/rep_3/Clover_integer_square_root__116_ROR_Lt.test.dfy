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

method {:test} Test2() {
var r0 := SquareRoot(4);
expect r0 * r0 <= 4 < (r0 + 1) * (r0 + 1);
}

// REPEAT 3 - TIME: 3.70319 s
