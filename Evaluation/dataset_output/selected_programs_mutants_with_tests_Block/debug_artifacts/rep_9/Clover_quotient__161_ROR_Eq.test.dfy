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

method {:test} Test8() {
expect 7728 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7728, 7728);
expect r1 * 7728 + r0 == 7728 && 0 <= r0 < 7728 && 0 <= r1;
}

// REPEAT 9 - TIME: 7.3353879 s
