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

method {:test} Test7() {
expect 1804 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1804);
expect r0 == 1804 * (1804 + 1) / 2;
}

// REPEAT 8 - TIME: 6.3143038 s
