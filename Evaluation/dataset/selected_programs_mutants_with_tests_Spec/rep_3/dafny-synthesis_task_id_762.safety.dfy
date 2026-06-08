method {:testEntry} IsMonthWith30Days(month: int) returns (result: bool)
    requires 1 <= month <= 12
    ensures result <==> month == 4 || month == 6 || month == 9 || month == 11
{
    result := month == 4 || month == 6 || month == 9 || month == 11;
}

method {:test} Test6() {
expect 1 <= 7 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(7);
expect r0 <==> 7 == 4 || 7 == 6 || 7 == 9 || 7 == 11;
}

// REPEAT 3 - TIME: 8.5517346 s
