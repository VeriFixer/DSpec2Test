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

// REPEAT 1 - TIME: 2.3252429 s

method {:test} Test1() {
var r0 := CountCharacters("a\0");
expect r0 >= 0;
expect r0 == |"a\0"|;
}

// REPEAT 2 - TIME: 3.2878772 s

method {:test} Test2() {
var r0 := CountCharacters("a\0aaaaaaaaaa\U{0002}");
expect r0 >= 0;
expect r0 == |"a\0aaaaaaaaaa\U{0002}"|;
}

// REPEAT 3 - TIME: 4.1106547 s

method {:test} Test3() {
var r0 := CountCharacters("\0\U{0002}aaaaaaaaaa\U{0004}");
expect r0 >= 0;
expect r0 == |"\0\U{0002}aaaaaaaaaa\U{0004}"|;
}

// REPEAT 4 - TIME: 5.0415917 s

method {:test} Test4() {
var r0 := CountCharacters("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"|;
}

// REPEAT 5 - TIME: 5.857006 s

method {:test} Test5() {
var r0 := CountCharacters("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"|;
}

// REPEAT 6 - TIME: 6.7251241 s

method {:test} Test6() {
var r0 := CountCharacters("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"|;
}

// REPEAT 7 - TIME: 7.5036932 s

method {:test} Test7() {
var r0 := CountCharacters("\U{0002}\0aaaaaaaaaaa\U{0004}");
expect r0 >= 0;
expect r0 == |"\U{0002}\0aaaaaaaaaaa\U{0004}"|;
}

// REPEAT 8 - TIME: 8.171954 s

method {:test} Test8() {
var r0 := CountCharacters("\U{0002}\0a");
expect r0 >= 0;
expect r0 == |"\U{0002}\0a"|;
}

// REPEAT 9 - TIME: 8.9328703 s

method {:test} Test9() {
var r0 := CountCharacters("\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
expect r0 == |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|;
}

// REPEAT 10 - TIME: 9.6429116 s
