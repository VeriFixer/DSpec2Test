method {:testEntry} IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
    requires costPrice >= 0 && sellingPrice >= 0
    ensures result <==> costPrice == sellingPrice
{
    result := costPrice == sellingPrice;
}

method {:test} Test16() {
expect 12 >= 0 && 12 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(12, 12);
expect r0 <==> 12 == 12;
}
method {:test} Test17() {
expect 13 >= 0 && 12 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(13, 12);
expect r0 <==> 13 == 12;
}

// REPEAT 9 - TIME: 12.1484423 s
