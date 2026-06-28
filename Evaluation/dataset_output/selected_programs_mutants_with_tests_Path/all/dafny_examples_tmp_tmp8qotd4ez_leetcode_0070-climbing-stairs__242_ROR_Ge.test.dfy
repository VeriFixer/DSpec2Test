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
  while i >= n
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

// REPEAT 1 - TIME: 4.7347886 s

method {:test} Test1() {
var r0 := ClimbStairs(2);
expect r0 == Stairs(2);
}

// REPEAT 2 - TIME: 7.8373526 s

method {:test} Test2() {
var r0 := ClimbStairs(3);
expect r0 == Stairs(3);
}

// REPEAT 3 - TIME: 10.2822175 s

method {:test} Test3() {
var r0 := ClimbStairs(4);
expect r0 == Stairs(4);
}

// REPEAT 4 - TIME: 12.878656 s

method {:test} Test4() {
var r0 := ClimbStairs(5858);
expect r0 == Stairs(5858);
}

// REPEAT 5 - TIME: 15.4504802 s

method {:test} Test5() {
var r0 := ClimbStairs(5859);
expect r0 == Stairs(5859);
}

// REPEAT 6 - TIME: 18.0404935 s

method {:test} Test6() {
var r0 := ClimbStairs(5860);
expect r0 == Stairs(5860);
}

// REPEAT 7 - TIME: 20.7180197 s

method {:test} Test7() {
var r0 := ClimbStairs(5861);
expect r0 == Stairs(5861);
}

// REPEAT 8 - TIME: 23.377648 s

method {:test} Test8() {
var r0 := ClimbStairs(5862);
expect r0 == Stairs(5862);
}

// REPEAT 9 - TIME: 25.9241439 s

method {:test} Test9() {
var r0 := ClimbStairs(5863);
expect r0 == Stairs(5863);
}

// REPEAT 10 - TIME: 28.6278854 s
