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

method {:test} Test6() {
expect 5 >= 0 && 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(5, 5);
expect (5 > 5 ==> r0 == 5 - 5) && (5 <= 5 ==> r0 == 0);
}
method {:test} Test7() {
expect 5 >= 0 && 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(5, 4);
expect (5 > 4 ==> r0 == 5 - 4) && (5 <= 4 ==> r0 == 0);
}

// REPEAT 4 - TIME: 9.2298527 s
