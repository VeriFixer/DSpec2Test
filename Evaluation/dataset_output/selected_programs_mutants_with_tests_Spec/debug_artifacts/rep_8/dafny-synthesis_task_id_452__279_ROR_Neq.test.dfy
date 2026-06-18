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

method {:test} Test14() {
expect 11 >= 0 && 11 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(11, 11);
expect (11 > 11 ==> r0 == 11 - 11) && (11 <= 11 ==> r0 == 0);
}
method {:test} Test15() {
expect 11 >= 0 && 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(11, 10);
expect (11 > 10 ==> r0 == 11 - 10) && (11 <= 10 ==> r0 == 0);
}

// REPEAT 8 - TIME: 14.3760515 s
