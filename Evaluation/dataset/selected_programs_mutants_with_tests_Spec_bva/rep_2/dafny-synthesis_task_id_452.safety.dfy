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

method {:test} Test16() {
expect 102 >= 0 && 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(102, 102);
expect (102 > 102 ==> r0 == 102 - 102) && (102 <= 102 ==> r0 == 0);
}
method {:test} Test17() {
expect 102 >= 0 && 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CalculateLoss(102, 101);
expect (102 > 101 ==> r0 == 102 - 101) && (102 <= 101 ==> r0 == 0);
}

// REPEAT 2 - TIME: 15.8623729 s
