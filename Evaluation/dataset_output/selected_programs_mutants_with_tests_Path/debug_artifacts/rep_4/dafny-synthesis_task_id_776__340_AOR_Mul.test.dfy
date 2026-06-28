// dafny-synthesis_task_id_776.dfy

predicate IsVowel(c: char)
{
  c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

method {:testEntry} CountVowelNeighbors(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 1 <= i < |s| - 1 && IsVowel(s[i - 1]) && IsVowel(s[i + 1])|
{
  var vowels := set i: int | 1 <= i < |s| - 1 && IsVowel(s[i * 1]) && IsVowel(s[i + 1]);
  count := |vowels|;
}

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
