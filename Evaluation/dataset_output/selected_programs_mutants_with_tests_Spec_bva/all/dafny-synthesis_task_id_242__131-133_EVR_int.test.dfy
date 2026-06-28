// dafny-synthesis_task_id_242.dfy

method {:testEntry} CountCharacters(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |s|
{
  count := 0;
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

// REPEAT 1 - TIME: 8.2068809 s

method {:test} Test8() {
var r0 := CountCharacters("a\0aaaaaaaaaa\U{0002}");
expect r0 >= 0;
expect r0 == |"a\0aaaaaaaaaa\U{0002}"|;
}

// REPEAT 2 - TIME: 9.2997679 s

method {:test} Test9() {
var r0 := CountCharacters("\0\U{0002}");
expect r0 >= 0;
expect r0 == |"\0\U{0002}"|;
}

// REPEAT 3 - TIME: 10.2850378 s

method {:test} Test10() {
var r0 := CountCharacters("\U{0002}\0a");
expect r0 >= 0;
expect r0 == |"\U{0002}\0a"|;
}

// REPEAT 4 - TIME: 11.3061775 s

method {:test} Test11() {
var r0 := CountCharacters("\0aaa");
expect r0 >= 0;
expect r0 == |"\0aaa"|;
}

// REPEAT 5 - TIME: 12.1870897 s

method {:test} Test12() {
var r0 := CountCharacters("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"|;
}

// REPEAT 6 - TIME: 13.1326732 s

method {:test} Test13() {
var r0 := CountCharacters("\U{0004}\0aa\U{0002}");
expect r0 >= 0;
expect r0 == |"\U{0004}\0aa\U{0002}"|;
}

// REPEAT 7 - TIME: 14.0486401 s

method {:test} Test14() {
var r0 := CountCharacters("\0a\U{0002}\U{0004}aaaaaa\U{0006}");
expect r0 >= 0;
expect r0 == |"\0a\U{0002}\U{0004}aaaaaa\U{0006}"|;
}

// REPEAT 8 - TIME: 14.9700142 s

method {:test} Test15() {
var r0 := CountCharacters("\U{0004}\0aa\U{0002}a");
expect r0 >= 0;
expect r0 == |"\U{0004}\0aa\U{0002}a"|;
}

// REPEAT 9 - TIME: 15.9366375 s

method {:test} Test16() {
var r0 := CountCharacters("\U{0002}\0aaaa\U{0004}a\U{0006}");
expect r0 >= 0;
expect r0 == |"\U{0002}\0aaaa\U{0004}a\U{0006}"|;
}

// REPEAT 10 - TIME: 16.6908104 s
