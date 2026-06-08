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

method {:test} Test18() {
expect 103 >= 0 && 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(103, 103);
expect (103 > 103 ==> r0 == 103 - 103) && (103 <= 103 ==> r0 == 0);
}
method {:test} Test19() {
expect 104 >= 0 && 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(104, 103);
expect (104 > 103 ==> r0 == 104 - 103) && (104 <= 103 ==> r0 == 0);
}

// REPEAT 3 - TIME: 17.3939986 s
