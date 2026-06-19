// dafny-synthesis_task_id_776.dfy

predicate IsVowel(c: char)
{
  c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

method {:testEntry} CountVowelNeighbors(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 1 <= i < |s| - 1 && IsVowel(s[i - 1]) && IsVowel(s[i + 1])|
{
  var vowels := set i: int | 1 <= i < |s| - 1 && IsVowel(s[1]) && IsVowel(s[i + 1]);
  count := |vowels|;
}


method {:test} Test0() {
var r0 := CountVowelNeighbors("aaaaaOUOaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test1() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaIa\0aaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test2() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaa\0aaa");
expect r0 >= 0;
}
method {:test} Test3() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaaaUaO");
expect r0 >= 0;
}
method {:test} Test4() {
var r0 := CountVowelNeighbors("aaaaaaoaIaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 5.5369109 s

method {:test} Test5() {
var r0 := CountVowelNeighbors("\U{0006}aaaaaaaaaaaaaaaaaaaaaa\0\U{0002}aa\U{0004}");
expect r0 >= 0;
}
method {:test} Test6() {
var r0 := CountVowelNeighbors("\U{0001}aaaaaaaaaaaaaaaaaa\0");
expect r0 >= 0;
}
method {:test} Test7() {
var r0 := CountVowelNeighbors("\U{0003}aaaaaaaaaaaaa\0aaaaaaaaa\U{0001}");
expect r0 >= 0;
}
method {:test} Test8() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}");
expect r0 >= 0;
}
method {:test} Test9() {
var r0 := CountVowelNeighbors("\0aaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 9.5560485 s

method {:test} Test10() {
var r0 := CountVowelNeighbors("eaa");
expect r0 >= 0;
}
method {:test} Test11() {
var r0 := CountVowelNeighbors("a\U{0001}aaaaaaaaaa\0aaaaaaa\U{0005}aa\U{0007}\t\U{000B}\U{0003}");
expect r0 >= 0;
}
method {:test} Test12() {
var r0 := CountVowelNeighbors("\U{000B}\U{000C}\U{0002}\U{0001}\n\t\U{0008}\U{0007}\0\U{0006}\U{0005}\U{0004}\U{0003}");
expect r0 >= 0;
}
method {:test} Test13() {
var r0 := CountVowelNeighbors("a\0aaaaaaaaaaaaaaaa\U{0002}a\U{0004}aa\U{0006}a\U{0008}a");
expect r0 >= 0;
}
method {:test} Test14() {
var r0 := CountVowelNeighbors("\U{0004}\0a\U{0001}aaaaa\U{0002}a");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 13.560099 s

method {:test} Test15() {
var r0 := CountVowelNeighbors("\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test16() {
var r0 := CountVowelNeighbors("\U{0005}\U{0001}a\U{0002}aaaaaaa\0aaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test17() {
var r0 := CountVowelNeighbors("\U{0005}\U{0001}a\U{0002}aaaaaaaaaaaaaaa\0aaaaaaa");
expect r0 >= 0;
}
method {:test} Test18() {
var r0 := CountVowelNeighbors("\U{0004}\0a\U{0001}aaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test19() {
var r0 := CountVowelNeighbors("\U{0006}\0a\U{0001}aaaaaa\U{0002}\U{0004}");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 18.5115714 s

method {:test} Test20() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test21() {
var r0 := CountVowelNeighbors("a\U{0001}aaaaaaaaaaaaaa\0aa\U{0005}aaa\U{0003}aaa\U{000B}\U{0007}\t");
expect r0 >= 0;
}
method {:test} Test22() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}aaaaaaaaaaaaaaa\0aaaaa\U{0007}a\t\U{0005}a");
expect r0 >= 0;
}
method {:test} Test23() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaa\U{0004}aaaaaaaaaaaa\U{0006}\U{0008}a");
expect r0 >= 0;
}
method {:test} Test24() {
var r0 := CountVowelNeighbors("a\0aaaaaaaaaaaaaa\U{0003}aaaaaa\U{0001}aaa\U{0005}\U{0007}a");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 24.1284694 s

method {:test} Test25() {
var r0 := CountVowelNeighbors("\U{0004}\0a\U{0001}aaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test26() {
var r0 := CountVowelNeighbors("\U{0006}\U{0001}a\U{0002}aaaaaaaaaaaaaaaa\0a");
expect r0 >= 0;
}
method {:test} Test27() {
var r0 := CountVowelNeighbors("\U{0006}\U{0001}a\U{0002}aaaaaaaaaaaaaaa\0aa");
expect r0 >= 0;
}
method {:test} Test29() {
var r0 := CountVowelNeighbors("\0aaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 29.5662498 s

method {:test} Test30() {
var r0 := CountVowelNeighbors("\U{0006}aaaaaaaaaaaaa\0aaa\U{0004}\U{0002}a");
expect r0 >= 0;
}
method {:test} Test31() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}aaaaaaaaa\0aaaaaaa");
expect r0 >= 0;
}
method {:test} Test32() {
var r0 := CountVowelNeighbors("aaaaa\0aaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test33() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test34() {
var r0 := CountVowelNeighbors("a\0aaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 35.6086397 s

method {:test} Test35() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test36() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}aaa\0aaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test39() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 43.3013905 s

method {:test} Test40() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test41() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}aaa\0aaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test42() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}aa\0aaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 51.7990032 s

method {:test} Test45() {
var r0 := CountVowelNeighbors("\U{0005}\0a\U{0001}aaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test46() {
var r0 := CountVowelNeighbors("a\U{0001}aaaaaaa\0aaaaaaa");
expect r0 >= 0;
}
method {:test} Test47() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}aaaaaaaaa\0aaa");
expect r0 >= 0;
}
method {:test} Test48() {
var r0 := CountVowelNeighbors("a\0aaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test49() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 59.7698035 s
