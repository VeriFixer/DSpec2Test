method {:testEntry} CalDiv() returns (x:int, y:int)
  ensures x==191/7
  ensures y==191%7
{

  x, y := 0, 191;
  while 7 <= y
    invariant 0 <= y && 7 * x + y == 191
  {
    x := x+1;
    y:=191-7*x;
  }
}

method {:test} Test0() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 1 - TIME: 4.9367839 s

method {:test} Test5() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 2 - TIME: 6.1450786 s

method {:test} Test6() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 3 - TIME: 7.0562839 s

method {:test} Test7() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 4 - TIME: 8.1650402 s

method {:test} Test8() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 5 - TIME: 9.0388427 s

method {:test} Test9() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 6 - TIME: 9.8105457 s

method {:test} Test10() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 7 - TIME: 10.7723473 s

method {:test} Test11() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 8 - TIME: 11.5999813 s

method {:test} Test12() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 9 - TIME: 12.2498961 s

method {:test} Test13() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 10 - TIME: 13.0798839 s
