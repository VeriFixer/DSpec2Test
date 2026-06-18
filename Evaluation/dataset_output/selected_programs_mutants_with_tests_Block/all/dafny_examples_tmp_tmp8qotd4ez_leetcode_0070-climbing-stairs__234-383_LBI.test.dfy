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
  while i < n
    invariant i <= n || i == 1
    invariant a == Stairs(i - 1)
    invariant b == Stairs(i)
  {
    break;
    a, b := b, a + b;
    i := i + 1;
  }
  return b;
}


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
var r0 := ClimbStairs(1);
expect r0 == Stairs(1);
}

// REPEAT 1 - TIME: 2.9460485 s

method {:test} Test1() {
var r0 := ClimbStairs(4);
expect r0 == Stairs(4);
}

// REPEAT 2 - TIME: 3.9306727 s

method {:test} Test2() {
var r0 := ClimbStairs(614);
expect r0 == Stairs(614);
}

// REPEAT 3 - TIME: 4.9504436 s

method {:test} Test3() {
var r0 := ClimbStairs(615);
expect r0 == Stairs(615);
}

// REPEAT 4 - TIME: 6.0870192 s

method {:test} Test4() {
var r0 := ClimbStairs(616);
expect r0 == Stairs(616);
}

// REPEAT 5 - TIME: 7.0840037 s

method {:test} Test5() {
var r0 := ClimbStairs(617);
expect r0 == Stairs(617);
}

// REPEAT 6 - TIME: 7.9508838 s

method {:test} Test6() {
var r0 := ClimbStairs(618);
expect r0 == Stairs(618);
}

// REPEAT 7 - TIME: 8.8620523 s

method {:test} Test7() {
var r0 := ClimbStairs(619);
expect r0 == Stairs(619);
}

// REPEAT 8 - TIME: 9.7957831 s

method {:test} Test8() {
var r0 := ClimbStairs(620);
expect r0 == Stairs(620);
}

// REPEAT 9 - TIME: 10.6037037 s

method {:test} Test9() {
var r0 := ClimbStairs(621);
expect r0 == Stairs(621);
}

// REPEAT 10 - TIME: 11.3613844 s
