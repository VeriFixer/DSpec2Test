// dafny-synthesis_task_id_776.dfy

predicate IsVowel(c: char)
{
  c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

method {:testEntry} CountVowelNeighbors(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 1 <= i < |s| - 1 && IsVowel(s[i - 1]) && IsVowel(s[i + 1])|
{
  var vowels := set i: int | 1 == i < |s| - 1 && IsVowel(s[i - 1]) && IsVowel(s[i + 1]);
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

// REPEAT 1 - TIME: 8.2483377 s

method {:test} Test5() {
var r0 := CountVowelNeighbors("\U{0004}aaaaaaaaaaaaaaaaaaaaaa\0aaa\U{0002}");
expect r0 >= 0;
}
method {:test} Test6() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaa\0aaaaaaa\U{0001}\U{0003}aa\U{0005}");
expect r0 >= 0;
}
method {:test} Test7() {
var r0 := CountVowelNeighbors("\0aaa");
expect r0 >= 0;
}
method {:test} Test8() {
var r0 := CountVowelNeighbors("\U{0004}aaaaaaaaaaaaaaaaaaaaaa\0\U{0002}");
expect r0 >= 0;
}
method {:test} Test9() {
var r0 := CountVowelNeighbors("\U{0005}aaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 14.7207374 s

method {:test} Test10() {
var r0 := CountVowelNeighbors("\U{000E}aaaaaaaaaaaaaaaaaa\0aaa\U{0002}\U{0004}\U{0006}\n\U{0008}a\U{000C}");
expect r0 >= 0;
}
method {:test} Test11() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaa\0aa\U{0002}aaa\U{0004}\U{0006}\U{0008}\n\U{000C}\U{0010}\U{000E}");
expect r0 >= 0;
}
method {:test} Test12() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaa\0aaa\U{0005}\U{0007}\t\U{0003}\U{000B}\r\U{000F}");
expect r0 >= 0;
}
method {:test} Test13() {
var r0 := CountVowelNeighbors("\0aa");
expect r0 >= 0;
}
method {:test} Test14() {
var r0 := CountVowelNeighbors("eaa");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 23.3319876 s

method {:test} Test15() {
var r0 := CountVowelNeighbors("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\0aa");
expect r0 >= 0;
}
method {:test} Test16() {
var r0 := CountVowelNeighbors("\taa\0aaaaaaaaaa\U{0005}aaaaaaaaaa\U{0007}aa\U{0003}\U{0001}");
expect r0 >= 0;
}
method {:test} Test17() {
var r0 := CountVowelNeighbors("\taaaaaaaaa\U{0001}aaa\0aaaaaaaaaa\U{0005}aa\U{0007}\U{0003}");
expect r0 >= 0;
}
method {:test} Test18() {
var r0 := CountVowelNeighbors("\U{0008}aaaaaaaaaaaaaaa\U{0002}\U{0004}aaaa\0aa\U{0006}aa");
expect r0 >= 0;
}
method {:test} Test19() {
var r0 := CountVowelNeighbors("\U{000C}aaaaaaaaaaaaaaaaaa\U{0002}aaa\U{0004}a\U{0006}a\0\n\U{0008}");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 31.0065628 s

method {:test} Test20() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test21() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaa\0aaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test22() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaa\0aaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 37.7687715 s

method {:test} Test25() {
var r0 := CountVowelNeighbors("\0aaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test26() {
var r0 := CountVowelNeighbors("\U{0005}aaa\U{0001}aa\U{0003}aaaaaaaaaaa\0aa");
expect r0 >= 0;
}
method {:test} Test27() {
var r0 := CountVowelNeighbors("\U{0003}aaaaaaa\U{0001}aaaaaaaaa\0aaa");
expect r0 >= 0;
}
method {:test} Test28() {
var r0 := CountVowelNeighbors("\U{0004}aaa\U{0002}aaa\0aaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 45.8560324 s

method {:test} Test30() {
var r0 := CountVowelNeighbors("aaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test31() {
var r0 := CountVowelNeighbors("\U{0004}aaaaaa\0aaaaaaaa\U{0002}aaaa");
expect r0 >= 0;
}
method {:test} Test32() {
var r0 := CountVowelNeighbors("\U{0006}aaaaaaaaaaaaaa\0\U{0002}aaa\U{0004}");
expect r0 >= 0;
}
method {:test} Test33() {
var r0 := CountVowelNeighbors("\U{0004}aaaaaaaaaa\0aa\U{0002}aaaaaa");
expect r0 >= 0;
}
method {:test} Test34() {
var r0 := CountVowelNeighbors("\U{0004}aaaaaaaaaaaaaaaaaa\U{0002}\0");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 55.3677932 s

method {:test} Test35() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaa\0a");
expect r0 >= 0;
}
method {:test} Test36() {
var r0 := CountVowelNeighbors("aaaaaaaaa\0aaaaaaaaa\U{0001}");
expect r0 >= 0;
}
method {:test} Test37() {
var r0 := CountVowelNeighbors("a\0aaaa");
expect r0 >= 0;
}
method {:test} Test39() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 63.8105401 s

method {:test} Test40() {
var r0 := CountVowelNeighbors("a\0aaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test41() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}\0aaaaa");
expect r0 >= 0;
}
method {:test} Test42() {
var r0 := CountVowelNeighbors("aaaaa\0aaaaaaaaaa\U{0001}aa");
expect r0 >= 0;
}
method {:test} Test43() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaaaaaa\U{0004}");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 73.346023 s

method {:test} Test45() {
var r0 := CountVowelNeighbors("a\0aaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test46() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}aaaa\0aaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test47() {
var r0 := CountVowelNeighbors("aaaaaaa\0aaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test49() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 86.3787657 s
