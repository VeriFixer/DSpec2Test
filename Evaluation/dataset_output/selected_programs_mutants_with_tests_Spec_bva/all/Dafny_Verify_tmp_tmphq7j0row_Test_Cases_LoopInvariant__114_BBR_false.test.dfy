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

method {:test} Test32() {
expect 0 <= 101, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileLess(101);
expect r0 == 101;
}
method {:test} Test33() {
expect 0 <= 101, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileNotEqual(101);
expect r0 == 101;
}
method {:test} Test34() {
expect 0 <= 101, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileNotEqual(101);
expect r0 == 0;
}
method {:test} Test35() {
expect 0 <= 101, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileGreater(101);
expect r0 == 0;
}

// REPEAT 2 - TIME: 23.6217367 s

method {:test} Test36() {
expect 0 <= 102, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileLess(102);
expect r0 == 102;
}
method {:test} Test37() {
expect 0 <= 102, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileNotEqual(102);
expect r0 == 102;
}
method {:test} Test38() {
expect 0 <= 102, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileNotEqual(102);
expect r0 == 0;
}
method {:test} Test39() {
expect 0 <= 102, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileGreater(102);
expect r0 == 0;
}

// REPEAT 3 - TIME: 25.9329738 s

method {:test} Test40() {
expect 0 <= 103, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileLess(103);
expect r0 == 103;
}
method {:test} Test41() {
expect 0 <= 103, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileNotEqual(103);
expect r0 == 103;
}
method {:test} Test42() {
expect 0 <= 103, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileNotEqual(103);
expect r0 == 0;
}
method {:test} Test43() {
expect 0 <= 103, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileGreater(103);
expect r0 == 0;
}

// REPEAT 4 - TIME: 28.1844027 s

method {:test} Test44() {
expect 0 <= 104, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileLess(104);
expect r0 == 104;
}
method {:test} Test45() {
expect 0 <= 104, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileNotEqual(104);
expect r0 == 104;
}
method {:test} Test46() {
expect 0 <= 104, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileNotEqual(104);
expect r0 == 0;
}
method {:test} Test47() {
expect 0 <= 104, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileGreater(104);
expect r0 == 0;
}

// REPEAT 5 - TIME: 30.368273 s

method {:test} Test48() {
expect 0 <= 105, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileLess(105);
expect r0 == 105;
}
method {:test} Test49() {
expect 0 <= 105, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileNotEqual(105);
expect r0 == 105;
}
method {:test} Test50() {
expect 0 <= 105, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileNotEqual(105);
expect r0 == 0;
}
method {:test} Test51() {
expect 0 <= 105, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileGreater(105);
expect r0 == 0;
}

// REPEAT 6 - TIME: 32.5567354 s

method {:test} Test52() {
expect 0 <= 106, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileLess(106);
expect r0 == 106;
}
method {:test} Test53() {
expect 0 <= 106, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileNotEqual(106);
expect r0 == 106;
}
method {:test} Test54() {
expect 0 <= 106, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileNotEqual(106);
expect r0 == 0;
}
method {:test} Test55() {
expect 0 <= 106, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileGreater(106);
expect r0 == 0;
}

// REPEAT 7 - TIME: 34.9431513 s

method {:test} Test56() {
expect 0 <= 107, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileLess(107);
expect r0 == 107;
}
method {:test} Test57() {
expect 0 <= 107, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileNotEqual(107);
expect r0 == 107;
}
method {:test} Test58() {
expect 0 <= 107, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileNotEqual(107);
expect r0 == 0;
}
method {:test} Test59() {
expect 0 <= 107, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileGreater(107);
expect r0 == 0;
}

// REPEAT 8 - TIME: 37.5428487 s

method {:test} Test60() {
expect 0 <= 108, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileLess(108);
expect r0 == 108;
}
method {:test} Test61() {
expect 0 <= 108, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileNotEqual(108);
expect r0 == 108;
}
method {:test} Test62() {
expect 0 <= 108, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileNotEqual(108);
expect r0 == 0;
}
method {:test} Test63() {
expect 0 <= 108, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileGreater(108);
expect r0 == 0;
}

// REPEAT 9 - TIME: 39.9236609 s

method {:test} Test64() {
expect 0 <= 109, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileLess(109);
expect r0 == 109;
}
method {:test} Test65() {
expect 0 <= 109, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := UpWhileNotEqual(109);
expect r0 == 109;
}
method {:test} Test66() {
expect 0 <= 109, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileNotEqual(109);
expect r0 == 0;
}
method {:test} Test67() {
expect 0 <= 109, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DownWhileGreater(109);
expect r0 == 0;
}

// REPEAT 10 - TIME: 42.1508557 s
