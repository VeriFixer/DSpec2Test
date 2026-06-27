// dafny-synthesis_task_id_461.dfy

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

method {:testEntry} CountUppercase(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{
  var uppercase := set i: int | 0 < i < |s| && IsUpperCase(s[i]);
  count := |uppercase|;
}


method {:test} Test0() {
var r0 := CountUppercase("N");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 2.4693675 s

method {:test} Test1() {
var r0 := CountUppercase("a\0aaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 3.3116775 s

method {:test} Test2() {
var r0 := CountUppercase("\U{0001}\0aaaaaaaaaaDaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 4.2542467 s

method {:test} Test3() {
var r0 := CountUppercase("\U{0001}aaaaaaaaaaa\0aaaaaaaaaaDa\U{0002}");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 5.2798023 s

method {:test} Test4() {
var r0 := CountUppercase("aaaaaaaaaaaaaaaaaaaD");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 6.2836194 s

method {:test} Test5() {
var r0 := CountUppercase("\0aaaaaaaaaaaaaaaaaaD");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 7.0473686 s

method {:test} Test6() {
var r0 := CountUppercase("\U{0003}aaaaaaaaaaa\0aaaaaaaa\U{0001}aaa\U{0002}");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 7.7062798 s

method {:test} Test7() {
var r0 := CountUppercase("\U{0003}aaaaaaaaaaaaaaaaaaa\0aaaa\U{0001}\U{0002}");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 8.3410873 s

method {:test} Test8() {
var r0 := CountUppercase("\0aaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 9.0025829 s

method {:test} Test9() {
var r0 := CountUppercase("aaaaaaaGaaaaaaaaa\U{0001}aa\0\U{0002}aaa\U{0003}\U{0005}\U{0004}");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 9.7224805 s
