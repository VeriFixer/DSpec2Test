// dafny-synthesis_task_id_637.dfy

method {:testEntry} IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
  requires costPrice >= 0 && sellingPrice >= 0
  ensures result <==> costPrice == sellingPrice
{
  result := false;
}

method {:test} Test8() {
expect 9 >= 0 && 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(9, 8);
expect r0 <==> 9 == 8;
}

// REPEAT 9 - TIME: 11.03172 s
