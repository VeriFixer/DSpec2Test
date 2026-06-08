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

method {:test} Test0() {
var r0 := ClimbStairs(0);
expect r0 == Stairs(0);
}
method {:test} Test1() {
var r0 := ClimbStairs(100);
expect r0 == Stairs(100);
}
method {:test} Test3() {
var r0 := ClimbStairs(3);
expect r0 == Stairs(3);
}

// REPEAT 1 - TIME: 5.5398155 s