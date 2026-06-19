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

// REPEAT 1 - TIME: 2.3599563 s

method {:test} Test1() {
var r0 := CountCharacters("a\0");
expect r0 >= 0;
expect r0 == |"a\0"|;
}

// REPEAT 2 - TIME: 3.3385025 s

method {:test} Test2() {
var r0 := CountCharacters("a\0aaaaaaaaaa\U{0002}");
expect r0 >= 0;
expect r0 == |"a\0aaaaaaaaaa\U{0002}"|;
}

// REPEAT 3 - TIME: 4.1348855 s

method {:test} Test3() {
var r0 := CountCharacters("\0\U{0002}aaaaaaaaaa\U{0004}");
expect r0 >= 0;
expect r0 == |"\0\U{0002}aaaaaaaaaa\U{0004}"|;
}

// REPEAT 4 - TIME: 4.8143867 s

method {:test} Test4() {
var r0 := CountCharacters("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"|;
}

// REPEAT 5 - TIME: 5.6563189 s

method {:test} Test5() {
var r0 := CountCharacters("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"|;
}

// REPEAT 6 - TIME: 6.4601041 s

method {:test} Test6() {
var r0 := CountCharacters("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"|;
}

// REPEAT 7 - TIME: 7.2574193 s

method {:test} Test7() {
var r0 := CountCharacters("\U{0002}\0aaaaaaaaaaa\U{0004}");
expect r0 >= 0;
expect r0 == |"\U{0002}\0aaaaaaaaaaa\U{0004}"|;
}

// REPEAT 8 - TIME: 7.8434441 s

method {:test} Test8() {
var r0 := CountCharacters("\U{0002}\0a");
expect r0 >= 0;
expect r0 == |"\U{0002}\0a"|;
}

// REPEAT 9 - TIME: 8.4780564 s

method {:test} Test9() {
var r0 := CountCharacters("\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
expect r0 == |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|;
}

// REPEAT 10 - TIME: 9.0823081 s
