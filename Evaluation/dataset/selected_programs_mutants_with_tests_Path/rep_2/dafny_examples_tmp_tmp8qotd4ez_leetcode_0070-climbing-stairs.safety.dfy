function Stairs(n: nat): nat {
  if n <= 1 then 1 else Stairs(n - 2) + Stairs(n - 1)
}

// A simple specification
method {:testEntry} ClimbStairs(n: nat) returns (r: nat)
  ensures r == Stairs(n)
{
  var a, b := 1, 1;
  var i := 1;
  while i < n
    invariant i <= n || i == 1
    invariant a == Stairs(i - 1)
    invariant b == Stairs(i)
  {
    a, b := b, a + b;
    i := i + 1;
  }
  return b;
}

method {:test} Test1() {
var r0 := ClimbStairs(2);
expect r0 == Stairs(2);
}

// REPEAT 2 - TIME: 9.9571511 s
