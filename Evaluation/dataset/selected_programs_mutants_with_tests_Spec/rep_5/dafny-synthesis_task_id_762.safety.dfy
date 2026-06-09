method {:testEntry} IsMonthWith30Days(month: int) returns (result: bool)
    requires 1 <= month <= 12
    ensures result <==> month == 4 || month == 6 || month == 9 || month == 11
{
    result := month == 4 || month == 6 || month == 9 || month == 11;
}

method {:test} Test8() {
expect 1 <= 5 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(5);
expect r0 <==> 5 == 4 || 5 == 6 || 5 == 9 || 5 == 11;
}

// REPEAT 5 - TIME: 10.6101263 s
