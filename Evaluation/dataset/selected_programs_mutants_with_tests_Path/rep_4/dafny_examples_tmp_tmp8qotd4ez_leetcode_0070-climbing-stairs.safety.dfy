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

method {:test} Test3() {
var r0 := ClimbStairs(1);
expect r0 == Stairs(1);
}

// REPEAT 4 - TIME: 7.2793242 s
