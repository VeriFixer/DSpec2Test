// dafny-synthesis_task_id_238.dfy

method {:testEntry} CountNonEmptySubstrings(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |s| * (|s| + 1) / 2
{
  count := (|s| + 1) / 2;
}

method {:test} Test0() {
var r0 := CountNonEmptySubstrings("a");
expect r0 >= 0;
expect r0 == |"a"| * (|"a"| + 1) / 2;
}
method {:test} Test1() {
var r0 := CountNonEmptySubstrings("");
expect r0 >= 0;
expect r0 == |""| * (|""| + 1) / 2;
}
method {:test} Test3() {
var r0 := CountNonEmptySubstrings("aa");
expect r0 >= 0;
expect r0 == |"aa"| * (|"aa"| + 1) / 2;
}

// REPEAT 1 - TIME: 5.9325969 s
