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
var r0 := ClimbStairs(1);
expect r0 == Stairs(1);
}

// REPEAT 1 - TIME: 3.3031705 s

method {:test} Test1() {
var r0 := ClimbStairs(4);
expect r0 == Stairs(4);
}

// REPEAT 2 - TIME: 4.428064 s

method {:test} Test2() {
var r0 := ClimbStairs(614);
expect r0 == Stairs(614);
}

// REPEAT 3 - TIME: 5.6288735 s

method {:test} Test3() {
var r0 := ClimbStairs(615);
expect r0 == Stairs(615);
}

// REPEAT 4 - TIME: 6.8120427 s

method {:test} Test4() {
var r0 := ClimbStairs(616);
expect r0 == Stairs(616);
}

// REPEAT 5 - TIME: 7.9899228 s

method {:test} Test5() {
var r0 := ClimbStairs(617);
expect r0 == Stairs(617);
}

// REPEAT 6 - TIME: 9.1024004 s

method {:test} Test6() {
var r0 := ClimbStairs(618);
expect r0 == Stairs(618);
}

// REPEAT 7 - TIME: 9.956548 s

method {:test} Test7() {
var r0 := ClimbStairs(619);
expect r0 == Stairs(619);
}

// REPEAT 8 - TIME: 10.8052047 s

method {:test} Test8() {
var r0 := ClimbStairs(620);
expect r0 == Stairs(620);
}

// REPEAT 9 - TIME: 11.7187789 s

method {:test} Test9() {
var r0 := ClimbStairs(621);
expect r0 == Stairs(621);
}

// REPEAT 10 - TIME: 12.5841563 s
