// dafny-synthesis_task_id_637.dfy

method {:testEntry} IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
  requires costPrice >= 0 && sellingPrice >= 0
  ensures result <==> costPrice == sellingPrice
{
  result := costPrice <= sellingPrice;
}

method {:test} Test2() {
expect 3 >= 0 && 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(3, 2);
expect r0 <==> 3 == 2;
}

// REPEAT 3 - TIME: 2.3040659 s
