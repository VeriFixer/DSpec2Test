// Clover_quotient.dfy

method {:testEntry} Quotient(x: nat, y: nat)
    returns (r: int, q: int)
  requires y != 0
  ensures q * y + r == x && 0 <= r < y && 0 <= q
{
  r := x;
  q := 0;
  while y == r
    invariant q * y + r == x && r >= 0
    decreases r
  {
    r := r - y;
    q := q + 1;
  }
}

method {:test} Test3() {
expect 7723 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7723, 7723);
expect r1 * 7723 + r0 == 7723 && 0 <= r0 < 7723 && 0 <= r1;
}

// REPEAT 4 - TIME: 3.9411918 s
