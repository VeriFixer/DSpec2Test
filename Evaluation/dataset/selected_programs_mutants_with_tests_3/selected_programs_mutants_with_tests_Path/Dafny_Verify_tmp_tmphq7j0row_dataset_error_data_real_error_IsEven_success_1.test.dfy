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
expect 40 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(40);
expect r0 <==> even(40);
}
method {:test} Test1() {
expect 41 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(41);
expect r0 <==> even(41);
}
method {:test} Test2() {
expect 42 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := is_even(42);
expect r0 <==> even(42);
}
