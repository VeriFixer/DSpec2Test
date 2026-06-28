// dafny-synthesis_task_id_776.dfy

predicate IsVowel(c: char)
{
  c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

method {:testEntry} CountVowelNeighbors(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 1 <= i < |s| - 1 && IsVowel(s[i - 1]) && IsVowel(s[i + 1])|
{
  var vowels := set i: int | 1 <= i == |s| - 1 && IsVowel(s[i - 1]) && IsVowel(s[i + 1]);
  count := |vowels|;
}


method {:test} Test0() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaaaOaO");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 2.5384232 s

method {:test} Test1() {
var r0 := CountVowelNeighbors("\0aaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 3.3485931 s

method {:test} Test2() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 4.1660322 s

method {:test} Test3() {
var r0 := CountVowelNeighbors("\0aaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 5.225825 s

method {:test} Test4() {
var r0 := CountVowelNeighbors("\0aaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 6.1661557 s

method {:test} Test5() {
var r0 := CountVowelNeighbors("\0aaa");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 7.3337368 s

method {:test} Test6() {
var r0 := CountVowelNeighbors("eaa");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 8.4625118 s

method {:test} Test7() {
var r0 := CountVowelNeighbors("\0aaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 9.2812888 s

method {:test} Test8() {
var r0 := CountVowelNeighbors("\U{0002}aaaaaaaa\0aaaaa\U{0004}aaaaa\U{0006}");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 10.0103475 s

method {:test} Test9() {
var r0 := CountVowelNeighbors("\U{0004}aaa\U{0002}aaa\0aa");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 10.7438225 s
