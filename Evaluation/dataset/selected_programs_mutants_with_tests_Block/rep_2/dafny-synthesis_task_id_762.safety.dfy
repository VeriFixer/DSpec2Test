method {:testEntry} IsMonthWith30Days(month: int) returns (result: bool)
    requires 1 <= month <= 12
    ensures result <==> month == 4 || month == 6 || month == 9 || month == 11
{
    result := month == 4 || month == 6 || month == 9 || month == 11;
}

method {:test} Test3() {
expect 1 <= 10 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(10);
expect r0 <==> 10 == 4 || 10 == 6 || 10 == 9 || 10 == 11;
}
method {:test} Test4() {
expect 1 <= 9 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(9);
expect r0 <==> 9 == 4 || 9 == 6 || 9 == 9 || 9 == 11;
}

// REPEAT 2 - TIME: 4.8923196 s
