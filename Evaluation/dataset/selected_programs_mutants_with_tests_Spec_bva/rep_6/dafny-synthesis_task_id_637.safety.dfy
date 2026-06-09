method {:testEntry} IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
    requires costPrice >= 0 && sellingPrice >= 0
    ensures result <==> costPrice == sellingPrice
{
    result := costPrice == sellingPrice;
}

method {:test} Test26() {
expect 108 >= 0 && 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(108, 108);
expect r0 <==> 108 == 108;
}
method {:test} Test27() {
expect 109 >= 0 && 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(109, 108);
expect r0 <==> 109 == 108;
}

// REPEAT 6 - TIME: 13.066338 s
