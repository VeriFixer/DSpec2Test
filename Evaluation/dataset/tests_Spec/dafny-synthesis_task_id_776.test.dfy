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

// REPEAT 1 - TIME: 3.0174761 s

method {:test} Test1() {
var r0 := CountVowelNeighbors("a");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 4.0389289 s

method {:test} Test2() {
var r0 := CountVowelNeighbors("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 4.9990352 s

method {:test} Test3() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaa\0aa");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 6.0179619 s

method {:test} Test4() {
var r0 := CountVowelNeighbors("\U{0002}aaaaaaaaaaaaa\0");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 7.2194075 s

method {:test} Test5() {
var r0 := CountVowelNeighbors("aaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 8.2099049 s

method {:test} Test6() {
var r0 := CountVowelNeighbors("\U{0002}\0a");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 9.1703174 s

method {:test} Test7() {
var r0 := CountVowelNeighbors("\U{0002}\0a");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 10.3666192 s

method {:test} Test8() {
var r0 := CountVowelNeighbors("\U{0002}aa\0aaaa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 11.3409326 s

method {:test} Test9() {
var r0 := CountVowelNeighbors("\U{0004}\0a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 12.126686 s
