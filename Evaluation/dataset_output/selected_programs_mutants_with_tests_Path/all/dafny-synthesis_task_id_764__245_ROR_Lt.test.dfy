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
var r0 := CountDigits("aaaaaaa20");
expect r0 >= 0;
}
method {:test} Test1() {
var r0 := CountDigits("aaaaaa1a/");
expect r0 >= 0;
}
method {:test} Test2() {
var r0 := CountDigits("aaaaaa1aa");
expect r0 >= 0;
}
method {:test} Test3() {
var r0 := CountDigits("1");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 4.9482065 s

method {:test} Test4() {
var r0 := CountDigits("1\0a");
expect r0 >= 0;
}
method {:test} Test5() {
var r0 := CountDigits("\U{0019}\0aaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test6() {
var r0 := CountDigits("\U{0001}\0aaaaa");
expect r0 >= 0;
}
method {:test} Test7() {
var r0 := CountDigits("a\0aaaaaaaaaaaa2aaaaaaaaa\U{0001}aaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 8.1706287 s

method {:test} Test8() {
var r0 := CountDigits("\0aaaaaaaa22aaaa\U{0001}aaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
}
method {:test} Test9() {
var r0 := CountDigits("\U{0008}\0");
expect r0 >= 0;
}
method {:test} Test10() {
var r0 := CountDigits("\U{0001}aaaaaaaaaa\0aa\U{0003}aa\U{0002}a");
expect r0 >= 0;
}
method {:test} Test11() {
var r0 := CountDigits("\U{0001}aaaaa\0aaa\U{0003}aaaa\U{0002}aaaaaaa");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 11.4872769 s

method {:test} Test12() {
var r0 := CountDigits("\U{0001}aaaaa2\0");
expect r0 >= 0;
}
method {:test} Test13() {
var r0 := CountDigits("\U{0002}aa\U{0001}aaa\0\U{0003}\U{000B}\U{0004}");
expect r0 >= 0;
}
method {:test} Test14() {
var r0 := CountDigits("\U{0002}aaaaaaaaaa\U{0004}\U{0001}a\0\U{0005}aaa\U{0006}\U{0003}a");
expect r0 >= 0;
}
method {:test} Test15() {
var r0 := CountDigits("\U{0006}a\0aaaaaa\U{0003}aaa\U{0001}a\U{0004}a\U{0002}a\U{0005}");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 15.3388258 s

method {:test} Test16() {
var r0 := CountDigits("aaa\0aaaa4a7aaaaaaaa\U{0003}\U{0004}a\U{0005}\U{0006}a\U{0007}\U{0002}\U{0001}\U{0008}\t");
expect r0 >= 0;
}
method {:test} Test17() {
var r0 := CountDigits("aaa9\0aaa\U{0012}aaaaaaaaaa\U{0004}aa\U{0005}\U{0006}aa\U{0003}\U{0002}\U{0007}\U{0001}");
expect r0 >= 0;
}
method {:test} Test18() {
var r0 := CountDigits("\U{0008}aaaaaaaaaaa\U{0001}aaaaa\U{0002}\U{0003}\U{0004}a\U{0005}\U{0006}\0a\U{0007}");
expect r0 >= 0;
}
method {:test} Test19() {
var r0 := CountDigits("aaaaaaaa\U{0001}aaaaaa\0aaa4\U{0002}a\U{0003}\U{0004}a\U{0005}");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 19.6269405 s

method {:test} Test20() {
var r0 := CountDigits("\0a1aaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test21() {
var r0 := CountDigits("\U{0006}aaaaaaa\U{0002}aa\U{0001}\U{0002}a\U{0003}aaa\U{0004}\U{0005}\0");
expect r0 >= 0;
}
method {:test} Test22() {
var r0 := CountDigits("\U{0007}aa\U{0001}a\U{0002}aa\0aaaaa\U{0005}\U{0003}aa\U{0004}\U{0006}a");
expect r0 >= 0;
}
method {:test} Test23() {
var r0 := CountDigits("\taaaaaaaa\0\U{0006}aaa\U{0004}aaaaa\U{0003}a\U{0007}\U{0001}aa\U{0005}\U{0002}\U{0008}");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 24.3796542 s

method {:test} Test24() {
var r0 := CountDigits("\U{0007}aaaaaaa2aaaaaaa\U{0001}aaaa\U{0003}\U{0005}\U{0004}a\0a\U{0002}a\U{0006}");
expect r0 >= 0;
}
method {:test} Test25() {
var r0 := CountDigits("\0aaaaaaa\'a");
expect r0 >= 0;
}
method {:test} Test26() {
var r0 := CountDigits("\U{0004}aaaaaaaaaaaaaaaaaa\0aaaaaa\U{0002}\U{0003}\U{0001}a");
expect r0 >= 0;
}
method {:test} Test27() {
var r0 := CountDigits("\U{0004}aaaaaaaaaaaaaaa\U{0001}aaaaaaaa\0\U{0002}\U{0003}aa");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 29.2100022 s

method {:test} Test28() {
var r0 := CountDigits("\U{0004}aaaaaaaaaa4\0\U{0001}aaaaaaa\U{0002}aaaa\U{0003}");
expect r0 >= 0;
}
method {:test} Test29() {
var r0 := CountDigits("\U{0004}aaaaaaaaaa\U{0018}\0\U{0001}aaaaaaa\U{0002}aa\U{0003}aa");
expect r0 >= 0;
}
method {:test} Test30() {
var r0 := CountDigits("\U{0003}aaaaaaaaaaaaaaaaaaaa\0aa\U{0001}a\U{0002}");
expect r0 >= 0;
}
method {:test} Test31() {
var r0 := CountDigits("\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 34.276521 s

method {:test} Test32() {
var r0 := CountDigits("\0aaaaaaaaaaaaa0aaaaaaa2a");
expect r0 >= 0;
}
method {:test} Test33() {
var r0 := CountDigits("\0aaaaaaaaaaaaa\U{0008}aaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test34() {
var r0 := CountDigits("\0aaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test35() {
var r0 := CountDigits("\0aaaaaaaaaaaaa0aaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 40.5089344 s

method {:test} Test36() {
var r0 := CountDigits("\0aaaaaaaaaaaaa0aaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test37() {
var r0 := CountDigits("\0a\U{0019}aa4aaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test38() {
var r0 := CountDigits("\0aaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test39() {
var r0 := CountDigits("\0aaaaaaaa1aaaaa");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 47.0190826 s
