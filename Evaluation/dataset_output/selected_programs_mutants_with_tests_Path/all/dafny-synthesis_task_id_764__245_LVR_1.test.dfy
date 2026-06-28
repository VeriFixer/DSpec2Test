// dafny-synthesis_task_id_764.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} CountDigits(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
  var digits := set i: int | 1 <= i < |s| && IsDigit(s[i]);
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

// REPEAT 1 - TIME: 3.7978338 s

method {:test} Test4() {
var r0 := CountDigits("1\0aaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test5() {
var r0 := CountDigits("\U{0019}\0a");
expect r0 >= 0;
}
method {:test} Test6() {
var r0 := CountDigits("\U{0001}\0a");
expect r0 >= 0;
}
method {:test} Test7() {
var r0 := CountDigits("\U{0001}\0aaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 6.8901447 s

method {:test} Test8() {
var r0 := CountDigits("aaa\U{0001}a\U{0002}aaa47aaa\0aaa\U{0003}a");
expect r0 >= 0;
}
method {:test} Test9() {
var r0 := CountDigits("\0\U{0019}");
expect r0 >= 0;
}
method {:test} Test10() {
var r0 := CountDigits("aaa\0aaaaaaaaaa\U{0003}aa\U{0002}aaaa\U{0001}a9a\U{0004}a\U{0005}");
expect r0 >= 0;
}
method {:test} Test11() {
var r0 := CountDigits("\0a");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 9.2840539 s

method {:test} Test12() {
var r0 := CountDigits("0");
expect r0 >= 0;
}
method {:test} Test13() {
var r0 := CountDigits("\U{0002}aa\"\0\U{0001}a");
expect r0 >= 0;
}
method {:test} Test14() {
var r0 := CountDigits("\U{0002}aaa\0a\U{0001}");
expect r0 >= 0;
}
method {:test} Test15() {
var r0 := CountDigits("\U{0002}aa\U{0001}aa\0a");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 11.7087482 s

method {:test} Test16() {
var r0 := CountDigits("\U{0005}a\0aaaa\U{0001}\U{0004}\U{0003}a\U{0007}7a\U{0006}aaaaa\U{0002}");
expect r0 >= 0;
}
method {:test} Test17() {
var r0 := CountDigits("\U{0006}\0aa\U{0003}aaa\U{0004}\ta2aaaaaaa\U{0007}\U{0008}aa\U{0001}\U{0002}\taaa\U{0005}");
expect r0 >= 0;
}
method {:test} Test18() {
var r0 := CountDigits("\U{0008}a\0aaa\U{0003}\U{0002}\U{0005}\U{0004}\U{0006}aaaaaaaa\U{0001}\U{0007}");
expect r0 >= 0;
}
method {:test} Test19() {
var r0 := CountDigits("\t\0a\U{0001}aaa\U{0006}aa\U{0002}aaa\U{0007}\U{0004}aa\U{0005}\U{0003}\U{0008}");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 14.5093681 s

method {:test} Test20() {
var r0 := CountDigits("\U{0001}aa4\0a");
expect r0 >= 0;
}
method {:test} Test21() {
var r0 := CountDigits("\U{0001}a\0\n");
expect r0 >= 0;
}
method {:test} Test22() {
var r0 := CountDigits("\U{0001}\0");
expect r0 >= 0;
}
method {:test} Test23() {
var r0 := CountDigits("\U{0002}a\U{0001}\0");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 17.736762 s

method {:test} Test24() {
var r0 := CountDigits("\naa\U{0002}aaaa9aaaaaa\U{0001}aaa\U{0004}\U{0008}\U{0005}a\U{0007}\0a\U{0003}a\U{0006}\t");
expect r0 >= 0;
}
method {:test} Test25() {
var r0 := CountDigits("\U{0007}aaaa\U{0002}aaaa\U{0004}aaa\0aaa\U{0002}a\U{0005}aa\U{0001}\U{0003}a\U{0006}aa");
expect r0 >= 0;
}
method {:test} Test26() {
var r0 := CountDigits("aaaaaaaaaaaa\U{0001}aaaaa\U{0004}a\U{0005}\0\U{0002}8a\U{0003}");
expect r0 >= 0;
}
method {:test} Test27() {
var r0 := CountDigits("\U{0006}aaaaaa\0aa\U{0003}a\U{0001}a\U{0004}a\U{0005}\U{0002}a");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 20.691328 s

method {:test} Test28() {
var r0 := CountDigits("aa\0aaaa\U{0002}aa4aaaaa\U{0001}aaaa\U{0003}8\U{0004}aaaa");
expect r0 >= 0;
}
method {:test} Test29() {
var r0 := CountDigits("\U{0006}aaaaaaa\U{0004}a\U{0003}\0aaa\U{0001}aaa\raaaaa\U{0002}a\U{0005}");
expect r0 >= 0;
}
method {:test} Test30() {
var r0 := CountDigits("aaaaaaaaaaaaaaaaaaaaa4aaaa\0a");
expect r0 >= 0;
}
method {:test} Test31() {
var r0 := CountDigits("\U{0008}aa\0aaaa\U{0004}aaaaa\U{0005}\U{0001}aa\U{0002}a\U{0003}aa\U{0006}aaa\U{0007}");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 23.6625445 s

method {:test} Test32() {
var r0 := CountDigits("\0aaaaaaa1aaa");
expect r0 >= 0;
}
method {:test} Test33() {
var r0 := CountDigits("\U{0003}aaaaaaaaa\U{0019}aaaaaa\0a\U{0001}aaaaaa\U{0002}a");
expect r0 >= 0;
}
method {:test} Test34() {
var r0 := CountDigits("\U{0003}aaaaaaaaaaaa\0aaaaa\U{0001}aaaaaa\U{0002}");
expect r0 >= 0;
}
method {:test} Test35() {
var r0 := CountDigits("aaaaaaa4aaaaa\0aaaaa\U{0001}aaaaaa\U{0002}");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 27.5208665 s

method {:test} Test36() {
var r0 := CountDigits("\U{0002}aaaaaaaaa1aaaaaaaa\0aaaaaaa\U{0001}");
expect r0 >= 0;
}
method {:test} Test37() {
var r0 := CountDigits("\0aaaaaaa\U{0019}a");
expect r0 >= 0;
}
method {:test} Test38() {
var r0 := CountDigits("\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 31.5364063 s
