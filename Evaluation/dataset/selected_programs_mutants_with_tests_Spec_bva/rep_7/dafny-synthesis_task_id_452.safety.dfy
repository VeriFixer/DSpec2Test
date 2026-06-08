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

method {:test} Test26() {
expect 109 >= 0 && 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(109, 109);
expect (109 > 109 ==> r0 == 109 - 109) && (109 <= 109 ==> r0 == 0);
}
method {:test} Test27() {
expect 110 >= 0 && 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(110, 109);
expect (110 > 109 ==> r0 == 110 - 109) && (110 <= 109 ==> r0 == 0);
}

// REPEAT 7 - TIME: 22.3290313 s
