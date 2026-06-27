// dafny-synthesis_task_id_461.dfy

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

method {:testEntry} CountUppercase(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{
  var uppercase := set i: int | 0 == i < |s| && IsUpperCase(s[i]);
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

// REPEAT 1 - TIME: 5.6370469 s

method {:test} Test4() {
var r0 := CountUppercase("\U{0001}\0aaaaDa");
expect r0 >= 0;
}
method {:test} Test5() {
var r0 := CountUppercase("@Ga");
expect r0 >= 0;
}
method {:test} Test6() {
var r0 := CountUppercase("aGa");
expect r0 >= 0;
}
method {:test} Test7() {
var r0 := CountUppercase("aaaaD");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 9.1633348 s

method {:test} Test8() {
var r0 := CountUppercase("\U{0001}aD\0");
expect r0 >= 0;
}
method {:test} Test9() {
var r0 := CountUppercase("\U{000F}\0");
expect r0 >= 0;
}
method {:test} Test10() {
var r0 := CountUppercase("\U{0001}\0");
expect r0 >= 0;
}
method {:test} Test11() {
var r0 := CountUppercase("C\0");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 12.5089712 s

method {:test} Test12() {
var r0 := CountUppercase("\0aC\U{0001}");
expect r0 >= 0;
}
method {:test} Test13() {
var r0 := CountUppercase("\U{0001}W\U{0013}\0\U{0002}aa");
expect r0 >= 0;
}
method {:test} Test14() {
var r0 := CountUppercase("\0aa\U{0001}\U{0003}\U{0002}");
expect r0 >= 0;
}
method {:test} Test15() {
var r0 := CountUppercase("\U{0002}\0a\U{0001}\U{0004}\U{0003}");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 16.2255901 s

method {:test} Test16() {
var r0 := CountUppercase("\U{0004}aBa\U{0003}\U{0005}\U{0002}\U{0001}P\0aaa\U{0006}aaaa");
expect r0 >= 0;
}
method {:test} Test17() {
var r0 := CountUppercase("\U{0003}aa,a\0\U{0001}\U{0002}");
expect r0 >= 0;
}
method {:test} Test18() {
var r0 := CountUppercase("\U{0003}aa\0aa\U{0001}\U{0002}");
expect r0 >= 0;
}
method {:test} Test19() {
var r0 := CountUppercase("\U{0003}a\U{0001}\U{0002}aa\U{0005}\0Caa\U{0004}a");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 20.7858273 s

method {:test} Test20() {
var r0 := CountUppercase("aaaaaa\U{0001}E\U{0002}\U{0005}Q\U{0004}\U{0003}\0");
expect r0 >= 0;
}
method {:test} Test21() {
var r0 := CountUppercase("aa\0aaa\U{0002}C\U{0003}\U{0003}\U{0004}\U{0001}");
expect r0 >= 0;
}
method {:test} Test22() {
var r0 := CountUppercase("aaa\0\U{0002}aEaa\U{0001}\U{0003}aa\U{0005}a\U{0004}");
expect r0 >= 0;
}
method {:test} Test23() {
var r0 := CountUppercase("aaB\0aaaaaaa\U{0001}\U{0002}\U{0003}");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 24.9760041 s

method {:test} Test24() {
var r0 := CountUppercase("Paaaaaa\0aaaa\U{0002}\U{0001}\U{0003}a\U{0006}S\U{0007}a\U{0005}\U{0004}");
expect r0 >= 0;
}
method {:test} Test25() {
var r0 := CountUppercase("aaaS\U{0002}aa\0\U{0002}aaaa\U{0001}\U{0003}\U{0004}\U{0005}");
expect r0 >= 0;
}
method {:test} Test26() {
var r0 := CountUppercase("aaaaaFaaa\U{0002}a\0a\U{0005}\U{0003}\U{0004}\U{0001}");
expect r0 >= 0;
}
method {:test} Test27() {
var r0 := CountUppercase("aaaaaaaa\U{0003}aaaa\U{0001}\U{0004}a\U{0002}a\U{0005}\0A");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 29.4419479 s

method {:test} Test28() {
var r0 := CountUppercase("aaaaaaaaa\0aa\U{0002}\U{0003}aW\U{0001}aaaaA\U{0004}");
expect r0 >= 0;
}
method {:test} Test29() {
var r0 := CountUppercase("aaaaaCaaa\U{0001}aa\U{0003}\U{0004}a\U{0002}a\0aaa\U{0005}\U{0002}");
expect r0 >= 0;
}
method {:test} Test30() {
var r0 := CountUppercase("aaaa\U{0004}Qa\U{0003}aaa\U{0006}aaaaa\U{0008}aa\U{0007}\U{0005}\0\U{0001}\U{0002}aaaa");
expect r0 >= 0;
}
method {:test} Test31() {
var r0 := CountUppercase("aaaa\U{0001}aa\U{0002}aa\0\U{0003}aa\U{0005}Eaaaaa\U{0006}\U{0004}");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 33.3770683 s

method {:test} Test32() {
var r0 := CountUppercase("\0aaaaaaaGa");
expect r0 >= 0;
}
method {:test} Test33() {
var r0 := CountUppercase(" aaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test34() {
var r0 := CountUppercase("aaaaaaaaaaaaaaaaa\U{0001}aaa\U{0003}\U{0004}\U{0002}aGaaa\0");
expect r0 >= 0;
}
method {:test} Test35() {
var r0 := CountUppercase("\0aaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 38.3968798 s

method {:test} Test36() {
var r0 := CountUppercase("aaaaaBaaaaaaa\U{0001}K\0\U{0002}\U{0003}aaaa\U{0004}\U{0005}");
expect r0 >= 0;
}
method {:test} Test37() {
var r0 := CountUppercase("aaaaaaaaaaaaaG aa\0aaa\U{0001}aa");
expect r0 >= 0;
}
method {:test} Test38() {
var r0 := CountUppercase("aPaaaaaaaaaaaaaaaaa\0a\U{0001}a\U{0004}\U{0003}\U{0002}a");
expect r0 >= 0;
}
method {:test} Test39() {
var r0 := CountUppercase("aBaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}aa\0\U{0002}");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 43.0114999 s
