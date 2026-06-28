// dafny-synthesis_task_id_776.dfy

predicate IsVowel(c: char)
{
  c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

method {:testEntry} CountVowelNeighbors(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 1 <= i < |s| - 1 && IsVowel(s[i - 1]) && IsVowel(s[i + 1])|
{
}


method {:test} Test0() {
var r0 := CountVowelNeighbors("aaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test1() {
var r0 := CountVowelNeighbors("");
expect r0 >= 0;
}
method {:test} Test2() {
var r0 := CountVowelNeighbors("a");
expect r0 >= 0;
}
method {:test} Test3() {
var r0 := CountVowelNeighbors("aaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 9.0915035 s

method {:test} Test9() {
var r0 := CountVowelNeighbors("aa\0aaaaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 10.2365742 s

method {:test} Test10() {
var r0 := CountVowelNeighbors("\U{0004}a\0aaaaaa\U{0002}");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 11.2201937 s

method {:test} Test11() {
var r0 := CountVowelNeighbors("\U{0006}\0aaaaaa\U{0002}aaaaaaaaaaaaaaaaaaa\U{0004}");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 12.4562182 s

method {:test} Test12() {
var r0 := CountVowelNeighbors("\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaaaaa\0aaaaa");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 13.632278 s

method {:test} Test13() {
var r0 := CountVowelNeighbors("\U{0007}aaaaaaaaa\U{0003}\U{0005}aaaaaaaaaaaaaaaa\0\U{0001}");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 14.8378477 s

method {:test} Test14() {
var r0 := CountVowelNeighbors("\n\0a\U{0003}aaaaa\U{0007}\U{0001}\U{0005}");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 15.9573315 s

method {:test} Test15() {
var r0 := CountVowelNeighbors("\U{0002}aaaaaaaa\U{0004}aaaaaaaaaaaaaa\0aaa\U{0006}\U{0008}");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 16.9592827 s

method {:test} Test16() {
var r0 := CountVowelNeighbors("\U{0004}\0aaaaaaa\U{0002}a");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 17.8627075 s

method {:test} Test17() {
var r0 := CountVowelNeighbors("\U{0010}\0a\U{0001}aaaaa\U{0008}a\U{000C}aaaaaaa\U{0006}aaaaaa\U{0002}\n\U{0003}a");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 18.8684194 s
