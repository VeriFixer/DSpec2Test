method {:testEntry} IsMonthWith30Days(month: int) returns (result: bool)
    requires 1 <= month <= 12
    ensures result <==> month == 4 || month == 6 || month == 9 || month == 11
{
    result := month == 4 || month == 6 || month == 9 || month == 11;
}

method {:test} Test32() {
expect 1 <= 3 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(3);
expect r0 <==> 3 == 4 || 3 == 6 || 3 == 9 || 3 == 11;
}

// REPEAT 7 - TIME: 20.2976155 s
