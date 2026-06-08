// dafny-synthesis_task_id_637.dfy

method {:testEntry} IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
  requires costPrice >= 0 && sellingPrice >= 0
  ensures result <==> costPrice == sellingPrice
{
  result := false;
}

method {:test} Test7() {
expect 8 >= 0 && 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(8, 7);
expect r0 <==> 8 == 7;
}

// REPEAT 8 - TIME: 10.8280882 s
