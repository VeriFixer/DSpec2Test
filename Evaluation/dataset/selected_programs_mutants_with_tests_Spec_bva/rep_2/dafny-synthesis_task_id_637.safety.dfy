method {:testEntry} IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
    requires costPrice >= 0 && sellingPrice >= 0
    ensures result <==> costPrice == sellingPrice
{
    result := costPrice == sellingPrice;
}

method {:test} Test18() {
expect 102 >= 0 && 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(102, 102);
expect r0 <==> 102 == 102;
}
method {:test} Test19() {
expect 103 >= 0 && 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsBreakEven(103, 102);
expect r0 <==> 103 == 102;
}

// REPEAT 2 - TIME: 9.9646485 s
