// dafny-synthesis_task_id_764.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} CountDigits(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
  var digits := set i: int | 0 <= -i < |s| && IsDigit(s[i]);
  count := |digits|;
}


method {:test} Test0() {
var r0 := CountDigits("a");
expect r0 >= 0;
}
method {:test} Test1() {
var r0 := CountDigits("");
expect r0 >= 0;
}
method {:test} Test3() {
var r0 := CountDigits("aaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 6.0984021 s

method {:test} Test9() {
var r0 := CountDigits("\U{0001}\0aaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 7.1363638 s

method {:test} Test10() {
var r0 := CountDigits("\0aaaaaaa");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 8.1033769 s

method {:test} Test11() {
var r0 := CountDigits("\U{0001}aa\0aaaaaa");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 8.9535142 s

method {:test} Test12() {
var r0 := CountDigits("\U{0001}\0aaa");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 9.6398123 s

method {:test} Test13() {
var r0 := CountDigits("\0aaaaaaa");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 10.4342879 s

method {:test} Test14() {
var r0 := CountDigits("\U{0001}\0");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 11.422888 s

method {:test} Test15() {
var r0 := CountDigits("\U{0001}a\0aa\U{0002}");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 12.2065815 s

method {:test} Test16() {
var r0 := CountDigits("\U{0001}\0a");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 13.0457639 s

method {:test} Test17() {
var r0 := CountDigits("\0aaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 13.7376875 s
