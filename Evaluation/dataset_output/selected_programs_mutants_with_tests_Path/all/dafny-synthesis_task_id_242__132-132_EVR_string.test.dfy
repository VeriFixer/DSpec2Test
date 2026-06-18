// dafny-synthesis_task_id_242.dfy

method {:testEntry} CountCharacters(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |s|
{
  count := |""|;
}


method {:testEntry} CountCharacters(s: string) returns (count: int)
    ensures count >= 0
    ensures count == |s|
{
    count := |s|;
}

method {:test} Test0() {
var r0 := CountCharacters("");
expect r0 >= 0;
expect r0 == |""|;
}

// REPEAT 1 - TIME: 4.6989154 s

method {:test} Test1() {
var r0 := CountCharacters("a");
expect r0 >= 0;
expect r0 == |"a"|;
}

// REPEAT 2 - TIME: 6.5310842 s

method {:test} Test2() {
var r0 := CountCharacters("aa");
expect r0 >= 0;
expect r0 == |"aa"|;
}

// REPEAT 3 - TIME: 8.3265456 s

method {:test} Test3() {
var r0 := CountCharacters("a\0a");
expect r0 >= 0;
expect r0 == |"a\0a"|;
}

// REPEAT 4 - TIME: 9.9806986 s

method {:test} Test4() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 5 - TIME: 11.3464138 s

method {:test} Test5() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 6 - TIME: 12.4489996 s

method {:test} Test6() {
var r0 := CountCharacters("\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}");
expect r0 >= 0;
expect r0 == |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}"|;
}

// REPEAT 7 - TIME: 13.6710872 s

method {:test} Test7() {
var r0 := CountCharacters("\U{0002}\0a\U{0004}");
expect r0 >= 0;
expect r0 == |"\U{0002}\0a\U{0004}"|;
}

// REPEAT 8 - TIME: 15.0197799 s

method {:test} Test8() {
var r0 := CountCharacters("a\0aaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa\U{0004}");
expect r0 >= 0;
expect r0 == |"a\0aaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa\U{0004}"|;
}

// REPEAT 9 - TIME: 16.7574058 s

method {:test} Test9() {
var r0 := CountCharacters("\0aaaaaaaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
expect r0 == |"\0aaaaaaaaaaaaaaaaa\U{0002}"|;
}

// REPEAT 10 - TIME: 18.2780336 s
