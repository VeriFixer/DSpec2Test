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
var r0 := CountVowelNeighbors("aaaaaaaaOaOaaaaaaaaUaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test1() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaaaaIa\0aaaaaa");
expect r0 >= 0;
}
method {:test} Test2() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa");
expect r0 >= 0;
}
method {:test} Test3() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaUaO");
expect r0 >= 0;
}
method {:test} Test4() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaoaIaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 10.6470285 s

method {:test} Test5() {
var r0 := CountVowelNeighbors("\U{0002}aaaaaaaaaaaaaaa\0");
expect r0 >= 0;
}
method {:test} Test6() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaa\U{0003}aaaaaaaaaaaaa\0\U{0005}aaaaaaaaaaaa\U{0007}");
expect r0 >= 0;
}
method {:test} Test7() {
var r0 := CountVowelNeighbors("\taaaaaaaa\0aaaaaa\U{0003}aaaaaaaaaaaaaaaaaaa\U{0005}aaaaaaaaa\U{0007}");
expect r0 >= 0;
}
method {:test} Test8() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaa\U{0005}aaaaaa\U{0003}aaaaaaa\U{0007}");
expect r0 >= 0;
}
method {:test} Test9() {
var r0 := CountVowelNeighbors("\U{0005}aaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaa\U{0003}");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 18.6395032 s

method {:test} Test10() {
var r0 := CountVowelNeighbors("\U{0006}a\U{0008}aaaaaaaaaaaaa\0aaaaaaaaaaaaaa\U{0002}a");
expect r0 >= 0;
}
method {:test} Test11() {
var r0 := CountVowelNeighbors("aaa\U{0011}aaaaaaaaaaaa\U{0003}\U{0005}aaaaaaaaaaaa\0\U{0007}\raaaa\taaaa\U{000B}\U{000F}");
expect r0 >= 0;
}
method {:test} Test12() {
var r0 := CountVowelNeighbors("\U{0017}\U{0019}\U{001B}aaaaaaa\0a\U{0001}\U{0013}\U{0002}");
expect r0 >= 0;
}
method {:test} Test13() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaa\U{0001}\U{0003}aaaaaaaaaaaaa\U{0005}\U{000B}aaa\U{0007}aaaaaa\ra\U{000F}\taa\U{0011}");
expect r0 >= 0;
}
method {:test} Test14() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaa\U{0001}\U{0003}aaaaaaaaaaaaa\U{0005}aaaa\U{0007}aaaaaa\U{000B}a\r\taa\U{000F}");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 27.7928439 s

method {:test} Test15() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaa\0aaaaaaaaaa\U{0004}aaa");
expect r0 >= 0;
}
method {:test} Test16() {
var r0 := CountVowelNeighbors("\na\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}aa\0aa\U{0002}aaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test17() {
var r0 := CountVowelNeighbors("aaa\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaaaa\U{0002}\0aaaa\U{0004}aaaaa");
expect r0 >= 0;
}
method {:test} Test18() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test19() {
var r0 := CountVowelNeighbors("\U{0008}aaaa\naaaaaaaaaaaa\0aaaaaaaaaa\U{0004}a\U{0002}aaaaaaaaaaaaa\U{0006}aa");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 37.1840065 s

method {:test} Test20() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test21() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaa\U{0002}");
expect r0 >= 0;
}
method {:test} Test22() {
var r0 := CountVowelNeighbors("aaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 48.4581719 s

method {:test} Test25() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test26() {
var r0 := CountVowelNeighbors("aaa\0aaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test27() {
var r0 := CountVowelNeighbors("aaaaaaa\0aaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test28() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 61.1548466 s

method {:test} Test30() {
var r0 := CountVowelNeighbors("aaa");
expect r0 >= 0;
}
method {:test} Test31() {
var r0 := CountVowelNeighbors("a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a");
expect r0 >= 0;
}
method {:test} Test32() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}aaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test34() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 76.1706357 s

method {:test} Test35() {
var r0 := CountVowelNeighbors("a\U{0001}a");
expect r0 >= 0;
}
method {:test} Test36() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}aaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test37() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaa");
expect r0 >= 0;
}
method {:test} Test38() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test39() {
var r0 := CountVowelNeighbors("a\0a\U{0001}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 92.7547095 s

method {:test} Test40() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa");
expect r0 >= 0;
}
method {:test} Test41() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}\0aaa");
expect r0 >= 0;
}
method {:test} Test42() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test43() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test44() {
var r0 := CountVowelNeighbors("a\0a\U{0001}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 115.028383 s

method {:test} Test45() {
var r0 := CountVowelNeighbors("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test46() {
var r0 := CountVowelNeighbors("a\U{0001}\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test47() {
var r0 := CountVowelNeighbors("\U{0005}\U{0001}a\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test48() {
var r0 := CountVowelNeighbors("\U{0004}\0a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test49() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 138.130691 s
