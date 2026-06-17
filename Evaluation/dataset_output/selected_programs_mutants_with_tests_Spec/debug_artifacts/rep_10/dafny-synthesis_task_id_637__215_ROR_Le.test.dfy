// dafny-synthesis_task_id_637.dfy

method {:testEntry} IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
  requires costPrice >= 0 && sellingPrice >= 0
  ensures result <==> costPrice == sellingPrice
{
  result := costPrice <= sellingPrice;
}

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

// REPEAT 10 - TIME: 13.1098604 s
