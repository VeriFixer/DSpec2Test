// dafny-synthesis_task_id_637.dfy

method {:testEntry} IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
  requires costPrice >= 0 && sellingPrice >= 0
  ensures result <==> costPrice == sellingPrice
{
  result := costPrice < sellingPrice;
}

method {:test} Test9() {
expect 10 >= 0 && 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(10, 9);
expect r0 <==> 10 == 9;
}

// REPEAT 10 - TIME: 8.5963069 s
