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
