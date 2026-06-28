// dafny-synthesis_task_id_764.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} CountDigits(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
  var digits := set i: int | 0 < i < |s| && IsDigit(s[i]);
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

// REPEAT 1 - TIME: 9.2435671 s

method {:test} Test9() {
var r0 := CountDigits("\U{0001}\0aaaaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 10.4515647 s

method {:test} Test10() {
var r0 := CountDigits("\U{0001}\0aaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 11.5139972 s

method {:test} Test11() {
var r0 := CountDigits("\U{0001}a\0a");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 12.6686211 s

method {:test} Test12() {
var r0 := CountDigits("\U{0001}a\0aaaaa");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 13.7156991 s

method {:test} Test13() {
var r0 := CountDigits("\U{0002}aaa\0aaa\U{0001}");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 14.8757302 s

method {:test} Test14() {
var r0 := CountDigits("\0a");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 15.7738782 s

method {:test} Test15() {
var r0 := CountDigits("\U{0001}\0a");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 16.8147874 s

method {:test} Test16() {
var r0 := CountDigits("\0aa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 17.6407461 s

method {:test} Test17() {
var r0 := CountDigits("\0aaa\U{0001}aa\U{0002}\U{0003}");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 18.5471241 s
