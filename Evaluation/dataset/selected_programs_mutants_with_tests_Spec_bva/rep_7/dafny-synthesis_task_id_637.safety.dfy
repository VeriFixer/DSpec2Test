method {:testEntry} IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
    requires costPrice >= 0 && sellingPrice >= 0
    ensures result <==> costPrice == sellingPrice
{
    result := costPrice == sellingPrice;
}

method {:test} Test28() {
expect 110 >= 0 && 110 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(110, 110);
expect r0 <==> 110 == 110;
}
method {:test} Test29() {
expect 110 >= 0 && 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(110, 109);
expect r0 <==> 110 == 109;
}

// REPEAT 7 - TIME: 15.3707178 s
