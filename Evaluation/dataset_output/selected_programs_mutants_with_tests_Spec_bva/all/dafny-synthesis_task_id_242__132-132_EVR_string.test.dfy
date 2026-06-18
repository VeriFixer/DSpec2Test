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

// REPEAT 1 - TIME: 6.6429061 s

method {:test} Test8() {
var r0 := CountCharacters("a\0aaaaaaaaaa\U{0002}");
expect r0 >= 0;
expect r0 == |"a\0aaaaaaaaaa\U{0002}"|;
}

// REPEAT 2 - TIME: 7.5591529 s

method {:test} Test9() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 3 - TIME: 8.4636525 s

method {:test} Test10() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 4 - TIME: 9.2506989 s

method {:test} Test11() {
var r0 := CountCharacters("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"|;
}

// REPEAT 5 - TIME: 9.9253327 s

method {:test} Test12() {
var r0 := CountCharacters("\U{0002}\0aaa\U{0004}aaaaaaa\U{0006}");
expect r0 >= 0;
expect r0 == |"\U{0002}\0aaa\U{0004}aaaaaaa\U{0006}"|;
}

// REPEAT 6 - TIME: 10.7055249 s

method {:test} Test13() {
var r0 := CountCharacters("\U{0002}\0a");
expect r0 >= 0;
expect r0 == |"\U{0002}\0a"|;
}

// REPEAT 7 - TIME: 11.4006152 s

method {:test} Test14() {
var r0 := CountCharacters("\0aaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
expect r0 == |"\0aaaaaaaaaaaa\U{0002}"|;
}

// REPEAT 8 - TIME: 12.0076547 s

method {:test} Test15() {
var r0 := CountCharacters("\U{0004}\0\U{0002}\U{0006}");
expect r0 >= 0;
expect r0 == |"\U{0004}\0\U{0002}\U{0006}"|;
}

// REPEAT 9 - TIME: 12.66508 s

method {:test} Test16() {
var r0 := CountCharacters("\U{0002}\0a");
expect r0 >= 0;
expect r0 == |"\U{0002}\0a"|;
}

// REPEAT 10 - TIME: 13.3980107 s
