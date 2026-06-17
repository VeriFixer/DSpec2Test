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

// REPEAT 1 - TIME: 2.8705373 s

method {:test} Test1() {
var r0 := CountVowelNeighbors("a");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 3.8502145 s

method {:test} Test2() {
var r0 := CountVowelNeighbors("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 4.9074732 s

method {:test} Test3() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaa\0aa");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 5.988359 s

method {:test} Test4() {
var r0 := CountVowelNeighbors("\U{0002}aaaaaaaaaaaaa\0");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 7.0939532 s

method {:test} Test5() {
var r0 := CountVowelNeighbors("aaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 8.0369358 s

method {:test} Test6() {
var r0 := CountVowelNeighbors("\U{0002}\0a");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 8.8379492 s

method {:test} Test7() {
var r0 := CountVowelNeighbors("\U{0002}\0a");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 9.7511045 s

method {:test} Test8() {
var r0 := CountVowelNeighbors("\U{0002}aa\0aaaa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 10.487281 s

method {:test} Test9() {
var r0 := CountVowelNeighbors("\U{0004}\0a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 11.0876882 s
