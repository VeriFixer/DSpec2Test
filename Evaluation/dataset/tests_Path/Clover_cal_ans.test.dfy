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

// REPEAT 1 - TIME: 5.6336297 s

method {:test} Test1() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 2 - TIME: 9.6754628 s

method {:test} Test2() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 3 - TIME: 13.2442966 s

method {:test} Test3() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 4 - TIME: 16.6004457 s

method {:test} Test4() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 5 - TIME: 20.0560145 s

method {:test} Test5() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 6 - TIME: 23.3252657 s

method {:test} Test6() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 7 - TIME: 26.7930273 s

method {:test} Test7() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 8 - TIME: 30.5266129 s

method {:test} Test8() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 9 - TIME: 34.2058872 s

method {:test} Test9() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 10 - TIME: 37.3786665 s
