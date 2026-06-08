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

method {:test} Test10() {
expect 8 >= 0 && 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(8, 8);
expect (8 > 8 ==> r0 == 8 - 8) && (8 <= 8 ==> r0 == 0);
}
method {:test} Test11() {
expect 8 >= 0 && 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(8, 7);
expect (8 > 7 ==> r0 == 8 - 7) && (8 <= 7 ==> r0 == 0);
}

// REPEAT 6 - TIME: 8.0987535 s
