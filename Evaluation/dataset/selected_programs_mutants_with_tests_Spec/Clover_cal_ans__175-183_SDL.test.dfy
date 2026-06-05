// Clover_cal_ans.dfy

method {:testEntry} CalDiv() returns (x: int, y: int)
  ensures x == 191 / 7
  ensures y == 191 % 7
{
  x, y := 0, 191;
  while 7 <= y
    invariant 0 <= y && 7 * x + y == 191
  {
    y := 191 - 7 * x;
  }
}

method {:test} Test0() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 1 - TIME: 1.2607034 s

method {:test} Test1() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 2 - TIME: 1.6212785 s

method {:test} Test2() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 3 - TIME: 2.0255907 s

method {:test} Test3() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 4 - TIME: 2.4507278 s
