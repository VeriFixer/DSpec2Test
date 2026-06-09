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
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaOaO");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 2.655538 s

method {:test} Test1() {
var r0 := CountVowelNeighbors("\U{0001}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 3.6291112 s

method {:test} Test2() {
var r0 := CountVowelNeighbors("aaa");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 4.4716193 s

method {:test} Test3() {
var r0 := CountVowelNeighbors("aaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 5.2645877 s

method {:test} Test4() {
var r0 := CountVowelNeighbors("\U{0004}aa\0aaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 6.0824412 s

method {:test} Test5() {
var r0 := CountVowelNeighbors("\U{0002}aaaaaaaaaaaaaaa\0a");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 6.7443893 s

method {:test} Test6() {
var r0 := CountVowelNeighbors("\0aaa");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 7.477501 s

method {:test} Test7() {
var r0 := CountVowelNeighbors("a\0a");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 8.121494 s

method {:test} Test8() {
var r0 := CountVowelNeighbors("\U{0002}\0aaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaa\U{0008}");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 8.9155525 s

method {:test} Test9() {
var r0 := CountVowelNeighbors("\U{0005}\0aaa\U{0007}aaaaaaaaaa\U{0003}aa");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 9.5045183 s
