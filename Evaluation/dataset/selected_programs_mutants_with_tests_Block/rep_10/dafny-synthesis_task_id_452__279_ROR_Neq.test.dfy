// dafny-synthesis_task_id_452.dfy

method {:testEntry} CalculateLoss(costPrice: int, sellingPrice: int) returns (loss: int)
  requires costPrice >= 0 && sellingPrice >= 0
  ensures (costPrice > sellingPrice ==> loss == costPrice - sellingPrice) && (costPrice <= sellingPrice ==> loss == 0)
{
  if costPrice != sellingPrice {
    loss := costPrice - sellingPrice;
  } else {
    loss := 0;
  }
}

method {:test} Test18() {
expect 14 >= 0 && 14 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(14, 14);
expect (14 > 14 ==> r0 == 14 - 14) && (14 <= 14 ==> r0 == 0);
}
method {:test} Test19() {
expect 14 >= 0 && 13 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(14, 13);
expect (14 > 13 ==> r0 == 14 - 13) && (14 <= 13 ==> r0 == 0);
}

// REPEAT 10 - TIME: 10.8220466 s
