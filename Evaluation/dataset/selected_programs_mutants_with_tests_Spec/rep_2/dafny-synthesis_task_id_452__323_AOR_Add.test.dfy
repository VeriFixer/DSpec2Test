// dafny-synthesis_task_id_452.dfy

method {:testEntry} CalculateLoss(costPrice: int, sellingPrice: int) returns (loss: int)
  requires costPrice >= 0 && sellingPrice >= 0
  ensures (costPrice > sellingPrice ==> loss == costPrice - sellingPrice) && (costPrice <= sellingPrice ==> loss == 0)
{
  if costPrice > sellingPrice {
    loss := costPrice + sellingPrice;
  } else {
    loss := 0;
  }
}

method {:test} Test2() {
expect 2 >= 0 && 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(2, 2);
expect (2 > 2 ==> r0 == 2 - 2) && (2 <= 2 ==> r0 == 0);
}
method {:test} Test3() {
expect 2 >= 0 && 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(2, 1);
expect (2 > 1 ==> r0 == 2 - 1) && (2 <= 1 ==> r0 == 0);
}

// REPEAT 2 - TIME: 4.8671011 s
