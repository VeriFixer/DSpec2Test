// dafny-synthesis_task_id_637.dfy

method {:testEntry} IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
  requires costPrice >= 0 && sellingPrice >= 0
  ensures result <==> costPrice == sellingPrice
{
  result := costPrice <= sellingPrice;
}

method {:test} Test5() {
expect 6 >= 0 && 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(6, 5);
expect r0 <==> 6 == 5;
}

// REPEAT 6 - TIME: 5.7621395 s
