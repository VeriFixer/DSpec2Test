// dafny-synthesis_task_id_637.dfy

method {:testEntry} IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
  requires costPrice >= 0 && sellingPrice >= 0
  ensures result <==> costPrice == sellingPrice
{
  result := costPrice > sellingPrice;
}


method {:test} Test0() {
expect 0 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(0, 0);
expect r0 <==> 0 == 0;
}
method {:test} Test1() {
expect 1 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(1, 0);
expect r0 <==> 1 == 0;
}

// REPEAT 1 - TIME: 3.2541427 s

method {:test} Test2() {
expect 2 >= 0 && 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(2, 2);
expect r0 <==> 2 == 2;
}
method {:test} Test3() {
expect 2 >= 0 && 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(2, 1);
expect r0 <==> 2 == 1;
}

// REPEAT 2 - TIME: 4.8687092 s

method {:test} Test4() {
expect 3 >= 0 && 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(3, 3);
expect r0 <==> 3 == 3;
}
method {:test} Test5() {
expect 4 >= 0 && 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(4, 3);
expect r0 <==> 4 == 3;
}

// REPEAT 3 - TIME: 6.0917265 s

method {:test} Test6() {
expect 5 >= 0 && 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(5, 5);
expect r0 <==> 5 == 5;
}
method {:test} Test7() {
expect 5 >= 0 && 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(5, 4);
expect r0 <==> 5 == 4;
}

// REPEAT 4 - TIME: 7.3306965 s

method {:test} Test8() {
expect 6 >= 0 && 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(6, 6);
expect r0 <==> 6 == 6;
}
method {:test} Test9() {
expect 7 >= 0 && 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(7, 6);
expect r0 <==> 7 == 6;
}

// REPEAT 5 - TIME: 8.6140024 s

method {:test} Test10() {
expect 8 >= 0 && 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(8, 8);
expect r0 <==> 8 == 8;
}
method {:test} Test11() {
expect 8 >= 0 && 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(8, 7);
expect r0 <==> 8 == 7;
}

// REPEAT 6 - TIME: 9.8757281 s

method {:test} Test12() {
expect 9 >= 0 && 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(9, 9);
expect r0 <==> 9 == 9;
}
method {:test} Test13() {
expect 10 >= 0 && 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(10, 9);
expect r0 <==> 10 == 9;
}

// REPEAT 7 - TIME: 11.0558527 s

method {:test} Test14() {
expect 11 >= 0 && 11 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(11, 11);
expect r0 <==> 11 == 11;
}
method {:test} Test15() {
expect 11 >= 0 && 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(11, 10);
expect r0 <==> 11 == 10;
}

// REPEAT 8 - TIME: 12.1877397 s

method {:test} Test16() {
expect 12 >= 0 && 12 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(12, 12);
expect r0 <==> 12 == 12;
}
method {:test} Test17() {
expect 13 >= 0 && 12 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(13, 12);
expect r0 <==> 13 == 12;
}

// REPEAT 9 - TIME: 13.2989754 s

method {:test} Test18() {
expect 14 >= 0 && 14 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(14, 14);
expect r0 <==> 14 == 14;
}
method {:test} Test19() {
expect 14 >= 0 && 13 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(14, 13);
expect r0 <==> 14 == 13;
}

// REPEAT 10 - TIME: 14.3443007 s
