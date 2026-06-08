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

method {:test} Test6() {
var r0 := ClimbStairs(101);
expect r0 == Stairs(101);
}

// REPEAT 2 - TIME: 6.4934765 s

method {:test} Test7() {
var r0 := ClimbStairs(102);
expect r0 == Stairs(102);
}

// REPEAT 3 - TIME: 7.3174307 s

method {:test} Test8() {
var r0 := ClimbStairs(103);
expect r0 == Stairs(103);
}

// REPEAT 4 - TIME: 7.9906254 s

method {:test} Test9() {
var r0 := ClimbStairs(104);
expect r0 == Stairs(104);
}

// REPEAT 5 - TIME: 8.666311 s

method {:test} Test10() {
var r0 := ClimbStairs(105);
expect r0 == Stairs(105);
}

// REPEAT 6 - TIME: 9.2673674 s

method {:test} Test11() {
var r0 := ClimbStairs(106);
expect r0 == Stairs(106);
}

// REPEAT 7 - TIME: 10.0498458 s

method {:test} Test12() {
var r0 := ClimbStairs(107);
expect r0 == Stairs(107);
}

// REPEAT 8 - TIME: 10.6271165 s

method {:test} Test13() {
var r0 := ClimbStairs(108);
expect r0 == Stairs(108);
}

// REPEAT 9 - TIME: 11.1403839 s

method {:test} Test14() {
var r0 := ClimbStairs(109);
expect r0 == Stairs(109);
}

// REPEAT 10 - TIME: 11.8478592 s
