// dafny-synthesis_task_id_776.dfy

predicate IsVowel(c: char)
{
  c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

method {:testEntry} CountVowelNeighbors(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 1 <= i < |s| - 1 && IsVowel(s[i - 1]) && IsVowel(s[i + 1])|
{
  var vowels := set i: int | 1 <= i <= |s| - 1 && IsVowel(s[i - 1]) && IsVowel(s[i + 1]);
  count := |vowels|;
}


method {:test} Test0() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaaaOaO");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 2.5785441 s

method {:test} Test1() {
var r0 := CountVowelNeighbors("\U{0002}\0aaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 3.4920147 s

method {:test} Test2() {
var r0 := CountVowelNeighbors("\U{0001}\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0003}");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 4.3336685 s

method {:test} Test3() {
var r0 := CountVowelNeighbors("\0aaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 5.2004637 s

method {:test} Test4() {
var r0 := CountVowelNeighbors("\U{0006}aaaaaaaaaaaaaa\0aaaa\U{0002}aaaaa\U{0004}");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 6.0646435 s

method {:test} Test5() {
var r0 := CountVowelNeighbors("\U{0002}aaaaaaaaaaaaaa\0");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 6.9946372 s

method {:test} Test6() {
var r0 := CountVowelNeighbors("\U{0002}aaaaaaaaaaaaaa\0a");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 7.9586283 s

method {:test} Test7() {
var r0 := CountVowelNeighbors("\U{0006}aaaaaaaaaaaaaa\0\U{0002}aaa\U{0004}");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 8.7829641 s

method {:test} Test8() {
var r0 := CountVowelNeighbors("\0aaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 9.5120163 s

method {:test} Test9() {
var r0 := CountVowelNeighbors("\U{0001}aaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 10.318392 s
