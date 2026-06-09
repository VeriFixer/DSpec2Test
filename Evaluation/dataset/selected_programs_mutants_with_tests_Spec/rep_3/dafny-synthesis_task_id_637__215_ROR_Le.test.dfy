// dafny-synthesis_task_id_637.dfy

method {:testEntry} IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
  requires costPrice >= 0 && sellingPrice >= 0
  ensures result <==> costPrice == sellingPrice
{
  result := costPrice <= sellingPrice;
}

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

// REPEAT 3 - TIME: 5.4214331 s
