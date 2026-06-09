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

method {:test} Test20() {
expect 105 >= 0 && 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(105, 105);
expect (105 > 105 ==> r0 == 105 - 105) && (105 <= 105 ==> r0 == 0);
}
method {:test} Test21() {
expect 105 >= 0 && 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(105, 104);
expect (105 > 104 ==> r0 == 105 - 104) && (105 <= 104 ==> r0 == 0);
}

// REPEAT 4 - TIME: 16.982544 s
