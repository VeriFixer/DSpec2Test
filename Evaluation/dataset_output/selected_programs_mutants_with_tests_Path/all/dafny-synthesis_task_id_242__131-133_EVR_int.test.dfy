// dafny-synthesis_task_id_242.dfy

method {:testEntry} CountCharacters(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |s|
{
  count := 0;
}


method {:test} Test0() {
var r0 := CountCharacters("");
expect r0 >= 0;
expect r0 == |""|;
}

// REPEAT 1 - TIME: 2.7987077 s

method {:test} Test1() {
var r0 := CountCharacters("a");
expect r0 >= 0;
expect r0 == |"a"|;
}

// REPEAT 2 - TIME: 3.8620891 s

method {:test} Test2() {
var r0 := CountCharacters("aa");
expect r0 >= 0;
expect r0 == |"aa"|;
}

// REPEAT 3 - TIME: 4.9588667 s

method {:test} Test3() {
var r0 := CountCharacters("a\0a");
expect r0 >= 0;
expect r0 == |"a\0a"|;
}

// REPEAT 4 - TIME: 5.9138757 s

method {:test} Test4() {
var r0 := CountCharacters("aaaa");
expect r0 >= 0;
expect r0 == |"aaaa"|;
}

// REPEAT 5 - TIME: 7.0129315 s

method {:test} Test5() {
var r0 := CountCharacters("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"|;
}

// REPEAT 6 - TIME: 7.8230265 s

method {:test} Test6() {
var r0 := CountCharacters("\U{0002}\0aaaaaaaaaaaa\U{0004}");
expect r0 >= 0;
expect r0 == |"\U{0002}\0aaaaaaaaaaaa\U{0004}"|;
}

// REPEAT 7 - TIME: 8.8477365 s

method {:test} Test7() {
var r0 := CountCharacters("\U{0002}\0aaaaaaaaaaaaa\U{0004}");
expect r0 >= 0;
expect r0 == |"\U{0002}\0aaaaaaaaaaaaa\U{0004}"|;
}

// REPEAT 8 - TIME: 9.9161944 s

method {:test} Test8() {
var r0 := CountCharacters("\U{0002}\0a");
expect r0 >= 0;
expect r0 == |"\U{0002}\0a"|;
}

// REPEAT 9 - TIME: 10.8983232 s

method {:test} Test9() {
var r0 := CountCharacters("\0aaa");
expect r0 >= 0;
expect r0 == |"\0aaa"|;
}

// REPEAT 10 - TIME: 11.8761452 s
