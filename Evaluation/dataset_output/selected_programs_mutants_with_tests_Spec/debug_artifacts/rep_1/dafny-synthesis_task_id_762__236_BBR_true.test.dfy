// dafny-synthesis_task_id_762.dfy

method {:testEntry} IsMonthWith30Days(month: int) returns (result: bool)
  requires 1 <= month <= 12
  ensures result <==> month == 4 || month == 6 || month == 9 || month == 11
{
  result := true;
}

method {:test} Test0() {
expect 1 <= 4 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(4);
expect r0 <==> 4 == 4 || 4 == 6 || 4 == 9 || 4 == 11;
}
method {:test} Test1() {
expect 1 <= 6 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(6);
expect r0 <==> 6 == 4 || 6 == 6 || 6 == 9 || 6 == 11;
}
method {:test} Test2() {
expect 1 <= 9 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(9);
expect r0 <==> 9 == 4 || 9 == 6 || 9 == 9 || 9 == 11;
}
method {:test} Test3() {
expect 1 <= 11 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(11);
expect r0 <==> 11 == 4 || 11 == 6 || 11 == 9 || 11 == 11;
}
method {:test} Test4() {
expect 1 <= 12 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsMonthWith30Days(12);
expect r0 <==> 12 == 4 || 12 == 6 || 12 == 9 || 12 == 11;
}

// REPEAT 1 - TIME: 4.6682683 s
