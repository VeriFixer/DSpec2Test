// dafny-synthesis_task_id_242.dfy

method {:testEntry} CountCharacters(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |s|
{
  count := |""|;
}


method {:test} Test0() {
var r0 := CountCharacters("a");
expect r0 >= 0;
expect r0 == |"a"|;
}

// REPEAT 1 - TIME: 2.9221771 s

method {:test} Test1() {
var r0 := CountCharacters("a\0");
expect r0 >= 0;
expect r0 == |"a\0"|;
}

// REPEAT 2 - TIME: 4.2802894 s

method {:test} Test2() {
var r0 := CountCharacters("aaaaaaaaaaaa\0");
expect r0 >= 0;
expect r0 == |"aaaaaaaaaaaa\0"|;
}

// REPEAT 3 - TIME: 5.220937 s

method {:test} Test3() {
var r0 := CountCharacters("a\0aaaaaaaa\U{0002}");
expect r0 >= 0;
expect r0 == |"a\0aaaaaaaa\U{0002}"|;
}

// REPEAT 4 - TIME: 6.0763907 s

method {:test} Test4() {
var r0 := CountCharacters("\U{0004}\0\U{0002}");
expect r0 >= 0;
expect r0 == |"\U{0004}\0\U{0002}"|;
}

// REPEAT 5 - TIME: 6.9865277 s

method {:test} Test5() {
var r0 := CountCharacters("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"|;
}

// REPEAT 6 - TIME: 7.6544127 s

method {:test} Test6() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 7 - TIME: 8.2778971 s

method {:test} Test7() {
var r0 := CountCharacters("\0\U{0002}a");
expect r0 >= 0;
expect r0 == |"\0\U{0002}a"|;
}

// REPEAT 8 - TIME: 8.8878707 s

method {:test} Test8() {
var r0 := CountCharacters("\U{0002}\0\U{0004}aaaaaa\U{0006}");
expect r0 >= 0;
expect r0 == |"\U{0002}\0\U{0004}aaaaaa\U{0006}"|;
}

// REPEAT 9 - TIME: 9.5606738 s

method {:test} Test9() {
var r0 := CountCharacters("\U{0002}aaa\U{0004}aaa\U{0006}aa\0aaa");
expect r0 >= 0;
expect r0 == |"\U{0002}aaa\U{0004}aaa\U{0006}aa\0aaa"|;
}

// REPEAT 10 - TIME: 10.1743385 s
