// Clover_quotient.dfy

method {:testEntry} Quotient(x: nat, y: nat)
    returns (r: int, q: int)
  requires y != 0
  ensures q * y + r == x && 0 <= r < y && 0 <= q
{
  r := x;
  q := 0;
  while false
    invariant q * y + r == x && r >= 0
    decreases r
  {
    r := r - y;
    q := q + 1;
  }
}

method {:test} Test1() {
expect 2 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(1, 2);
expect r1 * 2 + r0 == 1 && 0 <= r0 < 2 && 0 <= r1;
}

// REPEAT 2 - TIME: 3.9024057 s
