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
    break;
    r := r - y;
    q := q + 1;
  }
}

method {:test} Test6() {
expect 7 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(6, 7);
expect r1 * 7 + r0 == 6 && 0 <= r0 < 7 && 0 <= r1;
}

// REPEAT 7 - TIME: 17.0431165 s
