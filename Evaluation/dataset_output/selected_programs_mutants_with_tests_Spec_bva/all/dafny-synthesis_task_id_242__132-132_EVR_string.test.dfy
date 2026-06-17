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
var r0 := CountCharacters("a");
expect r0 >= 0;
expect r0 == |"a"|;
}
method {:test} Test1() {
var r0 := CountCharacters("");
expect r0 >= 0;
expect r0 == |""|;
}
method {:test} Test3() {
var r0 := CountCharacters("aa");
expect r0 >= 0;
expect r0 == |"aa"|;
}

// REPEAT 1 - TIME: 6.4094561 s

method {:test} Test8() {
var r0 := CountCharacters("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
expect r0 == |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|;
}

// REPEAT 2 - TIME: 7.251343 s

method {:test} Test9() {
var r0 := CountCharacters("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"|;
}

// REPEAT 3 - TIME: 8.151903 s

method {:test} Test10() {
var r0 := CountCharacters("\U{0004}\0\U{0002}");
expect r0 >= 0;
expect r0 == |"\U{0004}\0\U{0002}"|;
}

// REPEAT 4 - TIME: 8.8578554 s

method {:test} Test11() {
var r0 := CountCharacters("\0");
expect r0 >= 0;
expect r0 == |"\0"|;
}

// REPEAT 5 - TIME: 9.6264412 s

method {:test} Test12() {
var r0 := CountCharacters("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}");
expect r0 >= 0;
expect r0 == |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}"|;
}

// REPEAT 6 - TIME: 10.5565872 s

method {:test} Test13() {
var r0 := CountCharacters("\U{0006}\0\U{0004}\U{0002}");
expect r0 >= 0;
expect r0 == |"\U{0006}\0\U{0004}\U{0002}"|;
}

// REPEAT 7 - TIME: 11.3280357 s

method {:test} Test14() {
var r0 := CountCharacters("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a");
expect r0 >= 0;
expect r0 == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a"|;
}

// REPEAT 8 - TIME: 12.0889093 s

method {:test} Test15() {
var r0 := CountCharacters("\0");
expect r0 >= 0;
expect r0 == |"\0"|;
}

// REPEAT 9 - TIME: 12.9626031 s

method {:test} Test16() {
var r0 := CountCharacters("\0\U{0002}");
expect r0 >= 0;
expect r0 == |"\0\U{0002}"|;
}

// REPEAT 10 - TIME: 13.7950412 s
