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

// REPEAT 1 - TIME: 4.9741 s

method {:test} Test1() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 2 - TIME: 8.7318777 s

method {:test} Test2() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 3 - TIME: 12.0318967 s

method {:test} Test3() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 4 - TIME: 15.0206732 s

method {:test} Test4() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 5 - TIME: 17.9222582 s

method {:test} Test5() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 6 - TIME: 21.0231732 s

method {:test} Test6() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 7 - TIME: 24.2371375 s

method {:test} Test7() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 8 - TIME: 27.2234543 s

method {:test} Test8() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 9 - TIME: 30.5002429 s

method {:test} Test9() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 10 - TIME: 33.6487632 s
