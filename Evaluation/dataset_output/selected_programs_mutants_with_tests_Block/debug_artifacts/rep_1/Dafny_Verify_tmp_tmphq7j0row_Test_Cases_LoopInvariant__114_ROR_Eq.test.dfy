// Dafny_Verify_tmp_tmphq7j0row_Test_Cases_LoopInvariant.dfy

method {:testEntry} UpWhileLess(N: int) returns (i: int)
  requires 0 <= N
  ensures i == N
{
  i := 0;
  while i == N
    invariant 0 <= i <= N
    decreases N - i
  {
    i := i + 1;
  }
}

method {:testEntry} UpWhileNotEqual(N: int) returns (i: int)
  requires 0 <= N
  ensures i == N
{
  i := 0;
  while i != N
    invariant 0 <= i <= N
    decreases N - i
  {
    i := i + 1;
  }
}

method {:testEntry} DownWhileNotEqual(N: int) returns (i: int)
  requires 0 <= N
  ensures i == 0
{
  i := N;
  while i != 0
    invariant 0 <= i <= N
    decreases i
  {
    i := i - 1;
  }
}

method {:testEntry} DownWhileGreater(N: int) returns (i: int)
  requires 0 <= N
  ensures i == 0
{
  i := N;
  while 0 < i
    invariant 0 <= i <= N
    decreases i
  {
    i := i - 1;
  }
}

method {:testEntry} Quotient()
{
  var x, y := 0, 191;
  while 7 <= y
    invariant 0 <= y && 7 * x + y == 191
  {
    y := y - 7;
    x := x + 1;
  }
  assert x == 191 / 7 && y == 191 % 7;
}

method {:testEntry} Quotient1()
{
  var x, y := 0, 191;
  while 7 <= y
    invariant 0 <= y && 7 * x + y == 191
  {
    x, y := 27, 2;
  }
  assert x == 191 / 7 && y == 191 % 7;
}

method {:test} Test0() {
expect 0 <= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileLess(1);
expect r0 == 1;
}
method {:test} Test1() {
expect 0 <= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileNotEqual(1);
expect r0 == 1;
}
method {:test} Test2() {
expect 0 <= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileNotEqual(1);
expect r0 == 0;
}
method {:test} Test3() {
expect 0 <= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileGreater(1);
expect r0 == 0;
}
method {:test} Test4() {
Quotient();
}
method {:test} Test5() {
Quotient1();
}

// REPEAT 1 - TIME: 4.7867007 s
