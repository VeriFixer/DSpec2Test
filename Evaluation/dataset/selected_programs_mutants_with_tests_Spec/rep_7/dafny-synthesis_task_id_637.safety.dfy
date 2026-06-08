method {:testEntry} IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
    requires costPrice >= 0 && sellingPrice >= 0
    ensures result <==> costPrice == sellingPrice
{
    result := costPrice == sellingPrice;
}

method {:test} Test12() {
expect 9 >= 0 && 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(9, 9);
expect r0 <==> 9 == 9;
}
method {:test} Test13() {
expect 10 >= 0 && 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(10, 9);
expect r0 <==> 10 == 9;
}

// REPEAT 7 - TIME: 10.2463142 s
