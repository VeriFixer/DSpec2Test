// dafny-synthesis_task_id_452.dfy

method {:testEntry} CalculateLoss(costPrice: int, sellingPrice: int) returns (loss: int)
  requires costPrice >= 0 && sellingPrice >= 0
  ensures (costPrice > sellingPrice ==> loss == costPrice - sellingPrice) && (costPrice <= sellingPrice ==> loss == 0)
{
  if true {
    loss := costPrice - sellingPrice;
  } else {
    loss := 0;
  }
}

method {:test} Test16() {
expect 12 >= 0 && 12 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(12, 12);
expect (12 > 12 ==> r0 == 12 - 12) && (12 <= 12 ==> r0 == 0);
}
method {:test} Test17() {
expect 13 >= 0 && 12 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(13, 12);
expect (13 > 12 ==> r0 == 13 - 12) && (13 <= 12 ==> r0 == 0);
}

// REPEAT 9 - TIME: 10.5998089 s
