// dafny-synthesis_task_id_764.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} CountDigits(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
}


method {:test} Test0() {
var r0 := CountDigits("1");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 2.4888062 s

method {:test} Test1() {
var r0 := CountDigits("aaaaaaaaaaaa1aaaaaaaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 3.3403184 s

method {:test} Test2() {
var r0 := CountDigits("\0aaaaaaaaaaa1aaaaaaaa");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 4.1584251 s

method {:test} Test3() {
var r0 := CountDigits("\U{0002}\0aaaaaaaaaaaaaa0aaaa\U{0001}");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 4.9772832 s

method {:test} Test4() {
var r0 := CountDigits("\U{0003}aaaaaaaa\0aaaaaaaaaaa\U{0002}a\U{0001}");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 5.7549514 s

method {:test} Test5() {
var r0 := CountDigits("aaaaaaaaa\0aaa2aaaaaaa\U{0003}\U{0002}\U{0001}\U{0004}");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 6.8519848 s

method {:test} Test6() {
var r0 := CountDigits("\U{0002}aaaaaaaaaaa\0aaaaaaaa\U{0001}a1\U{0003}\U{0004}");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 7.8789662 s

method {:test} Test7() {
var r0 := CountDigits("a4aaaaaaaaa\0aaaaaaaaa\U{0002}\U{0003}a\U{0004}\U{0005}\U{0001}a");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 8.67931 s

method {:test} Test8() {
var r0 := CountDigits("\U{0001}aaaaaaaaaaaaa\0");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 9.615135 s

method {:test} Test9() {
var r0 := CountDigits("\0aaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 10.3837881 s
