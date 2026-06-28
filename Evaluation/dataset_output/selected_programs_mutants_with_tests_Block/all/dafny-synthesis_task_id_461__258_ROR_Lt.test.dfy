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

// REPEAT 1 - TIME: 2.7311581 s

method {:test} Test1() {
var r0 := CountUppercase("a\0aaaaaaaaaaaGaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 3.7035104 s

method {:test} Test2() {
var r0 := CountUppercase("aaaaaaDaa");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 4.4827455 s

method {:test} Test3() {
var r0 := CountUppercase("\U{0001}\0aaaaaaaaaaCaaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 5.3114271 s

method {:test} Test4() {
var r0 := CountUppercase("a\0aGa");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 6.2903567 s

method {:test} Test5() {
var r0 := CountUppercase("\U{0002}aaaaaaaaaaaaaaaa\U{0001}a\0aaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 7.0143673 s

method {:test} Test6() {
var r0 := CountUppercase("\U{0001}\0a");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 7.9097117 s

method {:test} Test7() {
var r0 := CountUppercase("\0a");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 8.6879278 s

method {:test} Test8() {
var r0 := CountUppercase("\U{0001}a\0a");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 9.4111705 s

method {:test} Test9() {
var r0 := CountUppercase("\0aa");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 10.0564803 s
