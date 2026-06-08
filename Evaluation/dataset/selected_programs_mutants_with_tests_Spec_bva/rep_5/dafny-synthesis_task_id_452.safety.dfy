method {:testEntry} CalculateLoss(costPrice: int, sellingPrice: int) returns (loss: int)
    requires costPrice >= 0 && sellingPrice >= 0
    ensures (costPrice > sellingPrice ==> loss == costPrice - sellingPrice) && (costPrice <= sellingPrice ==> loss == 0)
{
    if (costPrice > sellingPrice) {
        loss := costPrice - sellingPrice;
    } else {
        loss := 0;
    }
}

method {:test} Test22() {
expect 106 >= 0 && 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(106, 106);
expect (106 > 106 ==> r0 == 106 - 106) && (106 <= 106 ==> r0 == 0);
}
method {:test} Test23() {
expect 107 >= 0 && 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(107, 106);
expect (107 > 106 ==> r0 == 107 - 106) && (107 <= 106 ==> r0 == 0);
}

// REPEAT 5 - TIME: 19.8299656 s
