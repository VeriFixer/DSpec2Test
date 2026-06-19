// Clover_multi_return.dfy

method {:testEntry} MultipleReturns(x: int, y: int)
    returns (more: int, less: int)
  ensures more == x + y
  ensures less == x - y
{
  more := x;
  less := x - y;
}


method {:test} Test0() {
var r0, r1 := MultipleReturns(0, 0);
expect r0 == 0 + 0;
expect r1 == 0 - 0;
}

// REPEAT 1 - TIME: 2.1889088 s

method {:test} Test1() {
var r0, r1 := MultipleReturns(1, 1);
expect r0 == 1 + 1;
expect r1 == 1 - 1;
}

// REPEAT 2 - TIME: 3.0194502 s

method {:test} Test2() {
var r0, r1 := MultipleReturns(2, 2);
expect r0 == 2 + 2;
expect r1 == 2 - 2;
}

// REPEAT 3 - TIME: 4.1447257 s

method {:test} Test3() {
var r0, r1 := MultipleReturns(3, 3);
expect r0 == 3 + 3;
expect r1 == 3 - 3;
}

// REPEAT 4 - TIME: 4.9667341 s

method {:test} Test4() {
var r0, r1 := MultipleReturns(4, 4);
expect r0 == 4 + 4;
expect r1 == 4 - 4;
}

// REPEAT 5 - TIME: 5.8102474 s

method {:test} Test5() {
var r0, r1 := MultipleReturns(5, 5);
expect r0 == 5 + 5;
expect r1 == 5 - 5;
}

// REPEAT 6 - TIME: 6.650578 s

method {:test} Test6() {
var r0, r1 := MultipleReturns(6, 6);
expect r0 == 6 + 6;
expect r1 == 6 - 6;
}

// REPEAT 7 - TIME: 7.7027633 s

method {:test} Test7() {
var r0, r1 := MultipleReturns(7, 7);
expect r0 == 7 + 7;
expect r1 == 7 - 7;
}

// REPEAT 8 - TIME: 8.6340458 s

method {:test} Test8() {
var r0, r1 := MultipleReturns(8, 8);
expect r0 == 8 + 8;
expect r1 == 8 - 8;
}

// REPEAT 9 - TIME: 9.3651137 s

method {:test} Test9() {
var r0, r1 := MultipleReturns(9, 9);
expect r0 == 9 + 9;
expect r1 == 9 - 9;
}

// REPEAT 10 - TIME: 10.0484733 s
