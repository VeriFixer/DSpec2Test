// dafny-synthesis_task_id_637.dfy

method {:testEntry} IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
  requires costPrice >= 0 && sellingPrice >= 0
  ensures result <==> costPrice == sellingPrice
{
  result := costPrice >= sellingPrice;
}

method {:test} Test0() {
expect 1 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(1, 0);
expect r0 <==> 1 == 0;
}

// REPEAT 1 - TIME: 3.1889441 s
