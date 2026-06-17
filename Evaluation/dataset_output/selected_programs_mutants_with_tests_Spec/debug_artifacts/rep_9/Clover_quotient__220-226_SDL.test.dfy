// Clover_quotient.dfy

method {:testEntry} Quotient(x: nat, y: nat)
    returns (r: int, q: int)
  requires y != 0
  ensures q * y + r == x && 0 <= r < y && 0 <= q
{
  r := x;
  q := 0;
  while y <= r
    invariant q * y + r == x && r >= 0
    decreases r
  {
    q := q + 1;
  }
}

method {:test} Test8() {
expect 9 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(8, 9);
expect r1 * 9 + r0 == 8 && 0 <= r0 < 9 && 0 <= r1;
}

// REPEAT 9 - TIME: 9.7341239 s
