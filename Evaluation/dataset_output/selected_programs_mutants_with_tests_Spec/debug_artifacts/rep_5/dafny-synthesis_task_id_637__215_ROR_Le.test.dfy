// dafny-synthesis_task_id_637.dfy

method {:testEntry} IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
  requires costPrice >= 0 && sellingPrice >= 0
  ensures result <==> costPrice == sellingPrice
{
  result := costPrice <= sellingPrice;
}

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
