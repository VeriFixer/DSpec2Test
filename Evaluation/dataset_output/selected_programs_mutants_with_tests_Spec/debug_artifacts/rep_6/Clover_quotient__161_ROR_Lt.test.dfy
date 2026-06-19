// Clover_quotient.dfy

method {:testEntry} Quotient(x: nat, y: nat)
    returns (r: int, q: int)
  requires y != 0
  ensures q * y + r == x && 0 <= r < y && 0 <= q
{
  r := x;
  q := 0;
  while y < r
    invariant q * y + r == x && r >= 0
    decreases r
  {
    r := r - y;
    q := q + 1;
  }
}

method {:test} Test5() {
expect 6 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(5, 6);
expect r1 * 6 + r0 == 5 && 0 <= r0 < 6 && 0 <= r1;
}

// REPEAT 6 - TIME: 6.6236248 s
