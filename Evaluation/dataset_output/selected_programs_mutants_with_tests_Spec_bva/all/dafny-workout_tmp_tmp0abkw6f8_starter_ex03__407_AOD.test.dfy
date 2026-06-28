// dafny-workout_tmp_tmp0abkw6f8_starter_ex03.dfy

method {:testEntry} Abs(x: int) returns (y: int)
  requires x == -1
  ensures 0 <= y
  ensures 0 <= x ==> y == x
  ensures x < 0 ==> y == -x
{
  return x + 2;
}

method {:testEntry} Abs2(x: real) returns (y: real)
  requires x == -0.5
  ensures 0.0 <= y
  ensures 0.0 <= x ==> y == x
  ensures x < 0.0 ==> y == -x
{
  return x + 1.0;
}

method {:testEntry} Main()
{
  var a := Abs(-1);
  assert a == 1;
  var a2 := Abs2(0.5);
  assert a2 == 0.5;
}


method {:test} Test0() {
expect -1 == -1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Abs(-1);
expect 0 <= r0;
expect 0 <= -1 ==> r0 == -1;
expect -1 < 0 ==> r0 == --1;
}
method {:test} Test4() {
expect -1.0/2.0 == -0.5, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Abs2(-1.0/2.0);
expect 0.0 <= r0;
expect 0.0 <= -1.0/2.0 ==> r0 == -1.0/2.0;
expect -1.0/2.0 < 0.0 ==> r0 == --1.0/2.0;
}
method {:test} Test8() {
Main();
}

// REPEAT 1 - TIME: 9.1682874 s
