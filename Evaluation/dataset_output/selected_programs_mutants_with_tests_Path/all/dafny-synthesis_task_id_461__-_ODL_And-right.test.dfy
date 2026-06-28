// dafny-synthesis_task_id_461.dfy

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

method {:testEntry} CountUppercase(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{
  var uppercase := set i: int | 0 <= i < |s|;
  count := |uppercase|;
}


method {:test} Test0() {
var r0 := CountUppercase("aaaaaaaGC");
expect r0 >= 0;
}
method {:test} Test1() {
var r0 := CountUppercase("aaaaaaaG1");
expect r0 >= 0;
}
method {:test} Test2() {
var r0 := CountUppercase("aaaaaaDaa");
expect r0 >= 0;
}
method {:test} Test3() {
var r0 := CountUppercase("N");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 6.2510973 s

method {:test} Test4() {
var r0 := CountUppercase("D\0aaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test5() {
var r0 := CountUppercase("@Gaaaaa");
expect r0 >= 0;
}
method {:test} Test6() {
var r0 := CountUppercase("Gaaaaaa");
expect r0 >= 0;
}
method {:test} Test7() {
var r0 := CountUppercase("aaaaD");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 10.3321562 s

method {:test} Test8() {
var r0 := CountUppercase("E\0aa");
expect r0 >= 0;
}
method {:test} Test9() {
var r0 := CountUppercase("aaaaaaaaaaWa\U{0013}aa\U{0002}aa\0aaaaa\U{0001}\U{0003}");
expect r0 >= 0;
}
method {:test} Test10() {
var r0 := CountUppercase("\U{0005}\0aaaaa\U{0001}aaaaa\U{0002}a\U{0003}\U{0004}aaaaaaa");
expect r0 >= 0;
}
method {:test} Test11() {
var r0 := CountUppercase("a\0aaaaa\U{0002}aaaa\U{0001}aa\U{0005}aaaGaaaa\U{0004}\U{0003}");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 14.2281207 s

method {:test} Test12() {
var r0 := CountUppercase("\U{0001}aaaaaK\0");
expect r0 >= 0;
}
method {:test} Test13() {
var r0 := CountUppercase("\U{0010}\0");
expect r0 >= 0;
}
method {:test} Test14() {
var r0 := CountUppercase("\U{0004}aaaa\0aaaaaaaa\U{0001}a\U{0002}\U{0003}");
expect r0 >= 0;
}
method {:test} Test15() {
var r0 := CountUppercase("\U{0001}\0a");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 19.1458923 s

method {:test} Test16() {
var r0 := CountUppercase("\U{0003}aaa\0aa\U{0001}G\U{0002}");
expect r0 >= 0;
}
method {:test} Test17() {
var r0 := CountUppercase("aaaaaaaaaaa\U{000E}aaaaaa\U{0004}\U{0003}C\0aa\U{0005}\U{0001}\U{0002}a\U{0006}");
expect r0 >= 0;
}
method {:test} Test18() {
var r0 := CountUppercase("aaaaaaaa\U{0003}aaaaaaa\U{0001}\U{0002}\U{0005}aBaaa\U{0006}\0\U{0008}a\U{0007}\U{0004}");
expect r0 >= 0;
}
method {:test} Test19() {
var r0 := CountUppercase("aaaaaa\U{0002}aaaaaa\U{0001}a\0aa\U{0004}aB\U{0003}aa\U{0005}a\U{0006}");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 24.061755 s

method {:test} Test20() {
var r0 := CountUppercase("\U{0002}aGa\U{0001}\0");
expect r0 >= 0;
}
method {:test} Test21() {
var r0 := CountUppercase("\U{0004}aaaa,aa\U{0002}\U{0001}\0\U{0003}");
expect r0 >= 0;
}
method {:test} Test22() {
var r0 := CountUppercase("\U{0005}a\0aa\U{0002}a\U{0003}aa\U{0001}\U{0004}");
expect r0 >= 0;
}
method {:test} Test23() {
var r0 := CountUppercase("\U{0005}aaaaaaa\U{0002}a\U{0003}\U{0004}\U{0001}\0");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 29.2855573 s

method {:test} Test24() {
var r0 := CountUppercase("aCaaaaaaaaB\U{0003}aaa\0aa\U{0004}aaaa\U{0002}\U{0005}a\U{0006}\U{0001}");
expect r0 >= 0;
}
method {:test} Test25() {
var r0 := CountUppercase("\U{0001}a\0aaaaaaaaa\U{0010}");
expect r0 >= 0;
}
method {:test} Test26() {
var r0 := CountUppercase("\U{0002}aaaaaa\0aaaa\U{0001}");
expect r0 >= 0;
}
method {:test} Test27() {
var r0 := CountUppercase("\U{0002}aaaaaaaaa\0a\U{0001}");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 34.4244572 s

method {:test} Test28() {
var r0 := CountUppercase("\U{0001}aaaaaaaKa\0aaaa");
expect r0 >= 0;
}
method {:test} Test29() {
var r0 := CountUppercase("aaaaaaaaaaaFa\U{0001}a1a\U{0003}\U{0002}aa\0a");
expect r0 >= 0;
}
method {:test} Test30() {
var r0 := CountUppercase("\U{0006}aaaaaaaaaaaa\U{0001}\0a\U{0003}\U{0005}\U{0004}aa\U{0002}aaaaaa");
expect r0 >= 0;
}
method {:test} Test31() {
var r0 := CountUppercase("\U{0005}aaaaaaaaaaaa\U{0001}aaa\U{0003}aa\U{0004}a\0aa\U{0002}aa");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 39.9857709 s

method {:test} Test32() {
var r0 := CountUppercase("\U{0003}aaaaaaaaaCaa\0a\U{0001}aaaaaaa\U{0002}aaaa");
expect r0 >= 0;
}
method {:test} Test33() {
var r0 := CountUppercase("1aaaaaaaaaaa\0aa\U{0002}aa\U{0001}");
expect r0 >= 0;
}
method {:test} Test34() {
var r0 := CountUppercase("\U{0001}aaaaaaa\0aa");
expect r0 >= 0;
}
method {:test} Test35() {
var r0 := CountUppercase("\0aaaaa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 46.8258119 s

method {:test} Test36() {
var r0 := CountUppercase("aaaaaaaaaaaBaaaaGaaa\0a");
expect r0 >= 0;
}
method {:test} Test37() {
var r0 := CountUppercase("\U{0002}aaaaaaaaaaa\0aa aaaa\U{0001}aa");
expect r0 >= 0;
}
method {:test} Test38() {
var r0 := CountUppercase("aaaaaGaaaaaaaaaa\0aaaa\U{0001}");
expect r0 >= 0;
}
method {:test} Test39() {
var r0 := CountUppercase("aaaaaaaaaaaaaaaaaaC\0");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 54.1049633 s
