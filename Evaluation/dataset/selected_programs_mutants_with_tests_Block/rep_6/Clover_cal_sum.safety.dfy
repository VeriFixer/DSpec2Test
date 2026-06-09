method {:testEntry} Sum(N:int) returns (s:int)
  requires N >= 0
  ensures s == N * (N + 1) / 2
{
  var n := 0;
  s := 0;
  while n != N
    invariant 0 <= n <= N
    invariant s == n * (n + 1) / 2
  {
    n := n + 1;
    s := s + n;
  }
}

method {:test} Test5() {
expect 1802 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1802);
expect r0 == 1802 * (1802 + 1) / 2;
}

// REPEAT 6 - TIME: 5.0453798 s
