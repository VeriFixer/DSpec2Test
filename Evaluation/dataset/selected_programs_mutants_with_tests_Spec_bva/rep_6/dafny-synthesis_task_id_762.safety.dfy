method {:testEntry} IsMonthWith30Days(month: int) returns (result: bool)
    requires 1 <= month <= 12
    ensures result <==> month == 4 || month == 6 || month == 9 || month == 11
{
    result := month == 4 || month == 6 || month == 9 || month == 11;
}

method {:test} Test31() {
expect 1 <= 2 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(2);
expect r0 <==> 2 == 4 || 2 == 6 || 2 == 9 || 2 == 11;
}

// REPEAT 6 - TIME: 18.9203302 s
