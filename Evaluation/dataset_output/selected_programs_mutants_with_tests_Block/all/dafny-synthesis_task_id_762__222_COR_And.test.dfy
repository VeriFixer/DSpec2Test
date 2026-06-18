// dafny-synthesis_task_id_762.dfy

method {:testEntry} IsMonthWith30Days(month: int) returns (result: bool)
  requires 1 <= month <= 12
  ensures result <==> month == 4 || month == 6 || month == 9 || month == 11
{
  result := ((month == 4 || month == 6) && month == 9) || month == 11;
}


method {:testEntry} IsMonthWith30Days(month: int) returns (result: bool)
    requires 1 <= month <= 12
    ensures result <==> month == 4 || month == 6 || month == 9 || month == 11
{
    result := month == 4 || month == 6 || month == 9 || month == 11;
}

method {:test} Test0() {
expect 1 <= 12 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(12);
expect r0 <==> 12 == 4 || 12 == 6 || 12 == 9 || 12 == 11;
}
method {:test} Test1() {
expect 1 <= 6 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(6);
expect r0 <==> 6 == 4 || 6 == 6 || 6 == 9 || 6 == 11;
}
method {:test} Test2() {
expect 1 <= 4 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(4);
expect r0 <==> 4 == 4 || 4 == 6 || 4 == 9 || 4 == 11;
}

// REPEAT 1 - TIME: 3.1285952 s

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

// REPEAT 2 - TIME: 5.2641535 s

method {:test} Test7() {
expect 1 <= 7 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(7);
expect r0 <==> 7 == 4 || 7 == 6 || 7 == 9 || 7 == 11;
}
method {:test} Test8() {
expect 1 <= 11 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(11);
expect r0 <==> 11 == 4 || 11 == 6 || 11 == 9 || 11 == 11;
}

// REPEAT 3 - TIME: 7.2612616 s

method {:test} Test11() {
expect 1 <= 8 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(8);
expect r0 <==> 8 == 4 || 8 == 6 || 8 == 9 || 8 == 11;
}

// REPEAT 4 - TIME: 9.2586622 s

method {:test} Test15() {
expect 1 <= 5 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(5);
expect r0 <==> 5 == 4 || 5 == 6 || 5 == 9 || 5 == 11;
}

// REPEAT 5 - TIME: 10.7502785 s

method {:test} Test19() {
expect 1 <= 1 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(1);
expect r0 <==> 1 == 4 || 1 == 6 || 1 == 9 || 1 == 11;
}

// REPEAT 6 - TIME: 12.1579956 s

method {:test} Test23() {
expect 1 <= 2 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(2);
expect r0 <==> 2 == 4 || 2 == 6 || 2 == 9 || 2 == 11;
}

// REPEAT 7 - TIME: 13.3418331 s

method {:test} Test27() {
expect 1 <= 3 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(3);
expect r0 <==> 3 == 4 || 3 == 6 || 3 == 9 || 3 == 11;
}

// REPEAT 8 - TIME: 14.6784447 s
