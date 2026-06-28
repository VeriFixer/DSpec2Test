// dafny-synthesis_task_id_637.dfy

method {:testEntry} IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
  requires costPrice >= 0 && sellingPrice >= 0
  ensures result <==> costPrice == sellingPrice
{
  result := false;
}


method {:test} Test0() {
expect 1 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(1, 0);
expect r0 <==> 1 == 0;
}

// REPEAT 1 - TIME: 2.1131201 s

method {:test} Test1() {
expect 2 >= 0 && 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(2, 1);
expect r0 <==> 2 == 1;
}

// REPEAT 2 - TIME: 2.9257681 s

method {:test} Test2() {
expect 3 >= 0 && 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(3, 2);
expect r0 <==> 3 == 2;
}

// REPEAT 3 - TIME: 3.6776947 s

method {:test} Test3() {
expect 4 >= 0 && 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(4, 3);
expect r0 <==> 4 == 3;
}

// REPEAT 4 - TIME: 4.4821498 s

method {:test} Test4() {
expect 5 >= 0 && 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(5, 4);
expect r0 <==> 5 == 4;
}

// REPEAT 5 - TIME: 5.2203803 s

method {:test} Test5() {
expect 6 >= 0 && 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(6, 5);
expect r0 <==> 6 == 5;
}

// REPEAT 6 - TIME: 5.8967677 s

method {:test} Test6() {
expect 7 >= 0 && 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(7, 6);
expect r0 <==> 7 == 6;
}

// REPEAT 7 - TIME: 6.5647398 s

method {:test} Test7() {
expect 8 >= 0 && 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(8, 7);
expect r0 <==> 8 == 7;
}

// REPEAT 8 - TIME: 7.1216908 s

method {:test} Test8() {
expect 9 >= 0 && 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(9, 8);
expect r0 <==> 9 == 8;
}

// REPEAT 9 - TIME: 7.7407305 s

method {:test} Test9() {
expect 10 >= 0 && 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(10, 9);
expect r0 <==> 10 == 9;
}

// REPEAT 10 - TIME: 8.454166 s
