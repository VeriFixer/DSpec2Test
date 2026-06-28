// Dafny_Verify_tmp_tmphq7j0row_Test_Cases_LoopInvariant.dfy

method {:testEntry} UpWhileLess(N: int) returns (i: int)
  requires 0 <= N
  ensures i == N
{
  i := 0;
  while i < N
    invariant 0 <= i <= N
    decreases N - i
  {
    break;
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
expect 0 <= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileLess(0);
expect r0 == 0;
}
method {:test} Test2() {
expect 0 <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileLess(100);
expect r0 == 100;
}
method {:test} Test7() {
expect 0 <= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileNotEqual(0);
expect r0 == 0;
}
method {:test} Test9() {
expect 0 <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileNotEqual(100);
expect r0 == 100;
}
method {:test} Test14() {
expect 0 <= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileNotEqual(0);
expect r0 == 0;
}
method {:test} Test16() {
expect 0 <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileNotEqual(100);
expect r0 == 0;
}
method {:test} Test20() {
expect 0 <= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileGreater(0);
expect r0 == 0;
}
method {:test} Test22() {
expect 0 <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileGreater(100);
expect r0 == 0;
}
method {:test} Test26() {
Quotient();
}
method {:test} Test29() {
Quotient1();
}

// REPEAT 1 - TIME: 21.3937853 s
