// dafny-synthesis_task_id_637.dfy

method {:testEntry} IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
  requires costPrice >= 0 && sellingPrice >= 0
  ensures result <==> costPrice == sellingPrice
{
  result := costPrice >= sellingPrice;
}

method {:test} Test0() {
expect 0 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(0, 0);
expect r0 <==> 0 == 0;
}
method {:test} Test2() {
expect 100 >= 0 && 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(100, 100);
expect r0 <==> 100 == 100;
}
method {:test} Test9() {
expect 1 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(1, 0);
expect r0 <==> 1 == 0;
}
method {:test} Test10() {
expect 0 >= 0 && 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(0, 1);
expect r0 <==> 0 == 1;
}
method {:test} Test11() {
expect 100 >= 0 && 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(100, 101);
expect r0 <==> 100 == 101;
}
method {:test} Test13() {
expect 101 >= 0 && 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(101, 100);
expect r0 <==> 101 == 100;
}

// REPEAT 1 - TIME: 10.0161749 s
