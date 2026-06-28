// dafny-synthesis_task_id_776.dfy

predicate IsVowel(c: char)
{
  c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

method {:testEntry} CountVowelNeighbors(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 1 <= i < |s| - 1 && IsVowel(s[i - 1]) && IsVowel(s[i + 1])|
{
  var vowels := set i: int | 1 < i < |s| - 1 && IsVowel(s[i - 1]) && IsVowel(s[i + 1]);
  count := |vowels|;
}


method {:test} Test0() {
var r0 := CountVowelNeighbors("aaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 2.9290627 s

method {:test} Test1() {
var r0 := CountVowelNeighbors("\0");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 4.1392017 s

method {:test} Test2() {
var r0 := CountVowelNeighbors("aaaaaaaa");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 5.0278991 s

method {:test} Test3() {
var r0 := CountVowelNeighbors("\U{0002}a\0");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 5.9953111 s

method {:test} Test4() {
var r0 := CountVowelNeighbors("\U{0002}\0");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 7.0712609 s

method {:test} Test5() {
var r0 := CountVowelNeighbors("\U{0002}a\0aaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 7.9809782 s

method {:test} Test6() {
var r0 := CountVowelNeighbors("\U{0008}\0aaaaaa\U{0006}a\U{0004}aaaaaaaa\U{0002}aaaaaaaaa\n");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 8.9005487 s

method {:test} Test7() {
var r0 := CountVowelNeighbors("\U{0006}\0a\U{0004}aaaaa\U{0002}");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 9.8356757 s

method {:test} Test8() {
var r0 := CountVowelNeighbors("\U{0004}aa\0aaaaaaaaaaaaaaaaaaaaa\U{0002}a");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 10.8568641 s

method {:test} Test9() {
var r0 := CountVowelNeighbors("\U{0008}aaa\0aaaa\U{0004}aaa\U{0002}aaaaaaaaaaaa\U{0006}");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 11.7607169 s
