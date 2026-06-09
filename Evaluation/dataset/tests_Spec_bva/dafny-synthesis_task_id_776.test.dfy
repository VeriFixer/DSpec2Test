predicate IsVowel(c: char)
{
    c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

method {:testEntry} CountVowelNeighbors(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
{
    var vowels := set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]);
    count := |vowels|;
}

method {:test} Test0() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
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
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 5.8594161 s

method {:test} Test9() {
var r0 := CountVowelNeighbors("\U{0002}aaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 6.6227278 s

method {:test} Test10() {
var r0 := CountVowelNeighbors("\U{0002}\0aaaaa");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 7.2842077 s

method {:test} Test11() {
var r0 := CountVowelNeighbors("\U{0002}\0a");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 8.0854183 s

method {:test} Test12() {
var r0 := CountVowelNeighbors("\U{0002}\0");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 8.8355236 s

method {:test} Test13() {
var r0 := CountVowelNeighbors("\0a");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 9.5519745 s

method {:test} Test14() {
var r0 := CountVowelNeighbors("\U{0006}\0\U{0002}\U{0001}");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 10.2510179 s

method {:test} Test15() {
var r0 := CountVowelNeighbors("\naaaaaa\U{0006}\U{0004}aaaaaaaaaaaa\U{0002}aaaaaaaaaa\0a\U{0008}");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 11.0186955 s

method {:test} Test16() {
var r0 := CountVowelNeighbors("\na\0\U{0004}a\U{0006}\U{0002}\U{0008}");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 11.661129 s

method {:test} Test17() {
var r0 := CountVowelNeighbors("\naaa\0aa\U{0006}aaaaaaaaaa\U{0002}aaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaa\U{0008}");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 12.2883783 s
