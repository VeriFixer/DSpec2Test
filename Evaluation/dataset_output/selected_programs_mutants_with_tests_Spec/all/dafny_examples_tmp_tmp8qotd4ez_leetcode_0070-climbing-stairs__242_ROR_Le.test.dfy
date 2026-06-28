// dafny_examples_tmp_tmp8qotd4ez_leetcode_0070-climbing-stairs.dfy

function Stairs(n: nat): nat
{
  if n <= 1 then
    1
  else
    Stairs(n - 2) + Stairs(n - 1)
}

method {:testEntry} ClimbStairs(n: nat) returns (r: nat)
  ensures r == Stairs(n)
{
  var a, b := 1, 1;
  var i := 1;
  while i <= n
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

// REPEAT 1 - TIME: 2.7806605 s

method {:test} Test1() {
var r0 := ClimbStairs(1);
expect r0 == Stairs(1);
}

// REPEAT 2 - TIME: 3.6866094 s

method {:test} Test2() {
var r0 := ClimbStairs(2441);
expect r0 == Stairs(2441);
}

// REPEAT 3 - TIME: 4.6125351 s

method {:test} Test3() {
var r0 := ClimbStairs(2442);
expect r0 == Stairs(2442);
}

// REPEAT 4 - TIME: 5.495881 s

method {:test} Test4() {
var r0 := ClimbStairs(2443);
expect r0 == Stairs(2443);
}

// REPEAT 5 - TIME: 6.4731563 s

method {:test} Test5() {
var r0 := ClimbStairs(2444);
expect r0 == Stairs(2444);
}

// REPEAT 6 - TIME: 7.4123185 s

method {:test} Test6() {
var r0 := ClimbStairs(2445);
expect r0 == Stairs(2445);
}

// REPEAT 7 - TIME: 8.1639945 s

method {:test} Test7() {
var r0 := ClimbStairs(2446);
expect r0 == Stairs(2446);
}

// REPEAT 8 - TIME: 8.7881275 s

method {:test} Test8() {
var r0 := ClimbStairs(2447);
expect r0 == Stairs(2447);
}

// REPEAT 9 - TIME: 9.3850649 s

method {:test} Test9() {
var r0 := ClimbStairs(2448);
expect r0 == Stairs(2448);
}

// REPEAT 10 - TIME: 10.1187256 s
