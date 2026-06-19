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

// REPEAT 1 - TIME: 5.4215862 s

method {:test} Test6() {
var r0 := ClimbStairs(101);
expect r0 == Stairs(101);
}

// REPEAT 2 - TIME: 6.6334377 s

method {:test} Test7() {
var r0 := ClimbStairs(102);
expect r0 == Stairs(102);
}

// REPEAT 3 - TIME: 7.5578655 s

method {:test} Test8() {
var r0 := ClimbStairs(103);
expect r0 == Stairs(103);
}

// REPEAT 4 - TIME: 8.3379784 s

method {:test} Test9() {
var r0 := ClimbStairs(104);
expect r0 == Stairs(104);
}

// REPEAT 5 - TIME: 9.0803911 s

method {:test} Test10() {
var r0 := ClimbStairs(105);
expect r0 == Stairs(105);
}

// REPEAT 6 - TIME: 9.8517063 s

method {:test} Test11() {
var r0 := ClimbStairs(106);
expect r0 == Stairs(106);
}

// REPEAT 7 - TIME: 10.5289497 s

method {:test} Test12() {
var r0 := ClimbStairs(107);
expect r0 == Stairs(107);
}

// REPEAT 8 - TIME: 11.2530159 s

method {:test} Test13() {
var r0 := ClimbStairs(108);
expect r0 == Stairs(108);
}

// REPEAT 9 - TIME: 11.8238958 s

method {:test} Test14() {
var r0 := ClimbStairs(109);
expect r0 == Stairs(109);
}

// REPEAT 10 - TIME: 12.3824131 s
