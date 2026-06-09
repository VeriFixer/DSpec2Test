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

method {:test} Test3() {
expect 1800 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1800);
expect r0 == 1800 * (1800 + 1) / 2;
}

// REPEAT 4 - TIME: 3.7837 s
