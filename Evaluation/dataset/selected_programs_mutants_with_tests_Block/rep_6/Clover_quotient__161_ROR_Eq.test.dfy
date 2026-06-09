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

method {:test} Test5() {
expect 7725 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7725, 7725);
expect r1 * 7725 + r0 == 7725 && 0 <= r0 < 7725 && 0 <= r1;
}

// REPEAT 6 - TIME: 5.2138522 s
