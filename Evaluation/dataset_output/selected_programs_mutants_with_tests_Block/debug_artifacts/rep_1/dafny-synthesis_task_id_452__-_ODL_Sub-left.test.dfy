// dafny-synthesis_task_id_452.dfy

method {:testEntry} CalculateLoss(costPrice: int, sellingPrice: int) returns (loss: int)
  requires costPrice >= 0 && sellingPrice >= 0
  ensures (costPrice > sellingPrice ==> loss == costPrice - sellingPrice) && (costPrice <= sellingPrice ==> loss == 0)
{
  if costPrice > sellingPrice {
    loss := sellingPrice;
  } else {
    loss := 0;
  }
}

method {:test} Test0() {
expect 0 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(0, 0);
expect (0 > 0 ==> r0 == 0 - 0) && (0 <= 0 ==> r0 == 0);
}
method {:test} Test1() {
expect 1 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(1, 0);
expect (1 > 0 ==> r0 == 1 - 0) && (1 <= 0 ==> r0 == 0);
}

// REPEAT 1 - TIME: 2.5815842 s
