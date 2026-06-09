// dafny-synthesis_task_id_452.dfy

method {:testEntry} CalculateLoss(costPrice: int, sellingPrice: int) returns (loss: int)
  requires costPrice >= 0 && sellingPrice >= 0
  ensures (costPrice > sellingPrice ==> loss == costPrice - sellingPrice) && (costPrice <= sellingPrice ==> loss == 0)
{
  if costPrice < sellingPrice {
    loss := costPrice - sellingPrice;
  } else {
    loss := 0;
  }
}

method {:test} Test0() {
expect 0 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(0, 0);
expect (0 > 0 ==> r0 == 0 - 0) && (0 <= 0 ==> r0 == 0);
}
method {:test} Test2() {
expect 100 >= 0 && 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(100, 100);
expect (100 > 100 ==> r0 == 100 - 100) && (100 <= 100 ==> r0 == 0);
}
method {:test} Test4() {
expect 0 >= 0 && 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(0, 100);
expect (0 > 100 ==> r0 == 0 - 100) && (0 <= 100 ==> r0 == 0);
}
method {:test} Test8() {
expect 1 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(1, 0);
expect (1 > 0 ==> r0 == 1 - 0) && (1 <= 0 ==> r0 == 0);
}
method {:test} Test9() {
expect 100 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(100, 0);
expect (100 > 0 ==> r0 == 100 - 0) && (100 <= 0 ==> r0 == 0);
}
method {:test} Test11() {
expect 101 >= 0 && 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(101, 100);
expect (101 > 100 ==> r0 == 101 - 100) && (101 <= 100 ==> r0 == 0);
}

// REPEAT 1 - TIME: 12.9763781 s
