function even(n: int): bool
  requires n >= 0
{
  if n == 0 then true else !even(n-1)
}

method {:testEntry} is_even(n: int) returns (r: bool)
  requires n >= 0;
  ensures r <==> even(n);
{
  var i: int := 0;
  r := true;

  while i < n
    invariant 0 <= i <= n;
    invariant r <==> even(i);
  {
    r := !r;
    i := i + 1;
  }
}

method {:test} Test0() {
expect 7721 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7721);
expect r0 <==> even(7721);
}
method {:test} Test1() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(0);
expect r0 <==> even(0);
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(100);
expect r0 <==> even(100);
}

// REPEAT 1 - TIME: 9.4942077 s

method {:test} Test13() {
expect 7722 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7722);
expect r0 <==> even(7722);
}

// REPEAT 2 - TIME: 10.683181 s

method {:test} Test15() {
expect 7723 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7723);
expect r0 <==> even(7723);
}

// REPEAT 3 - TIME: 11.717343 s

method {:test} Test17() {
expect 7724 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7724);
expect r0 <==> even(7724);
}

// REPEAT 4 - TIME: 12.8622182 s

method {:test} Test19() {
expect 7725 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7725);
expect r0 <==> even(7725);
}

// REPEAT 5 - TIME: 13.7933374 s

method {:test} Test21() {
expect 7726 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7726);
expect r0 <==> even(7726);
}

// REPEAT 6 - TIME: 14.7184907 s

method {:test} Test23() {
expect 7727 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7727);
expect r0 <==> even(7727);
}

// REPEAT 7 - TIME: 15.6960864 s

method {:test} Test25() {
expect 7728 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7728);
expect r0 <==> even(7728);
}

// REPEAT 8 - TIME: 16.5790454 s

method {:test} Test27() {
expect 7729 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7729);
expect r0 <==> even(7729);
}

// REPEAT 9 - TIME: 17.4181007 s

method {:test} Test29() {
expect 7730 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(7730);
expect r0 <==> even(7730);
}

// REPEAT 10 - TIME: 18.2667064 s
