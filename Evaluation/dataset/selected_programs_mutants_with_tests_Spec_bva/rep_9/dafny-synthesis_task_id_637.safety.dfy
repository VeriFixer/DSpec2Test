method {:testEntry} IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
    requires costPrice >= 0 && sellingPrice >= 0
    ensures result <==> costPrice == sellingPrice
{
    result := costPrice == sellingPrice;
}

method {:test} Test32() {
expect 113 >= 0 && 113 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(113, 113);
expect r0 <==> 113 == 113;
}
method {:test} Test33() {
expect 113 >= 0 && 112 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(113, 112);
expect r0 <==> 113 == 112;
}

// REPEAT 9 - TIME: 16.8937933 s
