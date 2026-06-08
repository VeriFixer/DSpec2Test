method {:testEntry} IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
    requires costPrice >= 0 && sellingPrice >= 0
    ensures result <==> costPrice == sellingPrice
{
    result := costPrice == sellingPrice;
}

method {:test} Test34() {
expect 114 >= 0 && 114 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(114, 114);
expect r0 <==> 114 == 114;
}
method {:test} Test35() {
expect 115 >= 0 && 114 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(115, 114);
expect r0 <==> 115 == 114;
}

// REPEAT 10 - TIME: 17.8014892 s
