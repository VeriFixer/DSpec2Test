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
expect 4 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(3, 4);
expect r1 * 4 + r0 == 3 && 0 <= r0 < 4 && 0 <= r1;
}

// REPEAT 4 - TIME: 5.6016231 s
