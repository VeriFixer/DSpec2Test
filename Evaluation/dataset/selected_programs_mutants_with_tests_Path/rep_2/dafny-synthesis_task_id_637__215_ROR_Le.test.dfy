// dafny-synthesis_task_id_637.dfy

method {:testEntry} IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
  requires costPrice >= 0 && sellingPrice >= 0
  ensures result <==> costPrice == sellingPrice
{
  result := costPrice <= sellingPrice;
}

method {:test} Test1() {
expect 2 >= 0 && 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(2, 1);
expect r0 <==> 2 == 1;
}

// REPEAT 2 - TIME: 4.5747476 s
