// Dafny_Verify_tmp_tmphq7j0row_Test_Cases_LoopInvariant.dfy

method {:testEntry} UpWhileLess(N: int) returns (i: int)
  requires 0 <= N
  ensures i == N
{
  i := 0;
  while false
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
expect 0 <= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileLess(0);
expect r0 == 0;
}
method {:test} Test1() {
expect 0 <= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileNotEqual(0);
expect r0 == 0;
}
method {:test} Test2() {
expect 0 <= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileNotEqual(0);
expect r0 == 0;
}
method {:test} Test3() {
expect 0 <= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileGreater(0);
expect r0 == 0;
}
method {:test} Test4() {
Quotient();
}
method {:test} Test5() {
Quotient1();
}

// REPEAT 1 - TIME: 45.2444614 s

method {:test} Test6() {
expect 0 <= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileLess(1);
expect r0 == 1;
}
method {:test} Test7() {
expect 0 <= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileNotEqual(1);
expect r0 == 1;
}
method {:test} Test8() {
expect 0 <= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileNotEqual(1);
expect r0 == 0;
}
method {:test} Test9() {
expect 0 <= 1, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileGreater(1);
expect r0 == 0;
}

// REPEAT 2 - TIME: 67.6625065 s

method {:test} Test10() {
expect 0 <= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileLess(2);
expect r0 == 2;
}
method {:test} Test11() {
expect 0 <= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileNotEqual(2);
expect r0 == 2;
}
method {:test} Test12() {
expect 0 <= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileNotEqual(2);
expect r0 == 0;
}
method {:test} Test13() {
expect 0 <= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileGreater(2);
expect r0 == 0;
}

// REPEAT 3 - TIME: 90.554555 s

method {:test} Test14() {
expect 0 <= 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileLess(3);
expect r0 == 3;
}
method {:test} Test15() {
expect 0 <= 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileNotEqual(3);
expect r0 == 3;
}
method {:test} Test16() {
expect 0 <= 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileNotEqual(3);
expect r0 == 0;
}
method {:test} Test17() {
expect 0 <= 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileGreater(3);
expect r0 == 0;
}

// REPEAT 4 - TIME: 113.8009156 s

method {:test} Test18() {
expect 0 <= 4, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileLess(4);
expect r0 == 4;
}
method {:test} Test19() {
expect 0 <= 4, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileNotEqual(4);
expect r0 == 4;
}
method {:test} Test20() {
expect 0 <= 4, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileNotEqual(4);
expect r0 == 0;
}
method {:test} Test21() {
expect 0 <= 4, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileGreater(4);
expect r0 == 0;
}

// REPEAT 5 - TIME: 137.6310432 s

method {:test} Test22() {
expect 0 <= 5, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileLess(5);
expect r0 == 5;
}
method {:test} Test23() {
expect 0 <= 5, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileNotEqual(5);
expect r0 == 5;
}
method {:test} Test24() {
expect 0 <= 5, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileNotEqual(5);
expect r0 == 0;
}
method {:test} Test25() {
expect 0 <= 5, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileGreater(5);
expect r0 == 0;
}

// REPEAT 6 - TIME: 160.2610445 s

method {:test} Test26() {
expect 0 <= 6, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileLess(6);
expect r0 == 6;
}
method {:test} Test27() {
expect 0 <= 6, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileNotEqual(6);
expect r0 == 6;
}
method {:test} Test28() {
expect 0 <= 6, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileNotEqual(6);
expect r0 == 0;
}
method {:test} Test29() {
expect 0 <= 6, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileGreater(6);
expect r0 == 0;
}

// REPEAT 7 - TIME: 189.4150715 s

method {:test} Test30() {
expect 0 <= 7, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileLess(7);
expect r0 == 7;
}
method {:test} Test31() {
expect 0 <= 7, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileNotEqual(7);
expect r0 == 7;
}
method {:test} Test32() {
expect 0 <= 7, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileNotEqual(7);
expect r0 == 0;
}
method {:test} Test33() {
expect 0 <= 7, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileGreater(7);
expect r0 == 0;
}

// REPEAT 8 - TIME: 224.0098589 s

method {:test} Test34() {
expect 0 <= 8, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileLess(8);
expect r0 == 8;
}
method {:test} Test35() {
expect 0 <= 8, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileNotEqual(8);
expect r0 == 8;
}
method {:test} Test36() {
expect 0 <= 8, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileNotEqual(8);
expect r0 == 0;
}
method {:test} Test37() {
expect 0 <= 8, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileGreater(8);
expect r0 == 0;
}

// REPEAT 9 - TIME: 266.9574428 s

method {:test} Test38() {
expect 0 <= 9, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileLess(9);
expect r0 == 9;
}
method {:test} Test39() {
expect 0 <= 9, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileNotEqual(9);
expect r0 == 9;
}
method {:test} Test40() {
expect 0 <= 9, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileNotEqual(9);
expect r0 == 0;
}
method {:test} Test41() {
expect 0 <= 9, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileGreater(9);
expect r0 == 0;
}

// REPEAT 10 - TIME: 313.127373 s
