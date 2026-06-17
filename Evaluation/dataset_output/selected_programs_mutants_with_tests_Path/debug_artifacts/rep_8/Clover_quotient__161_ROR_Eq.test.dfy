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

method {:test} Test7() {
expect 8 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7, 8);
expect r1 * 8 + r0 == 7 && 0 <= r0 < 8 && 0 <= r1;
}

// REPEAT 8 - TIME: 34.8108055 s
