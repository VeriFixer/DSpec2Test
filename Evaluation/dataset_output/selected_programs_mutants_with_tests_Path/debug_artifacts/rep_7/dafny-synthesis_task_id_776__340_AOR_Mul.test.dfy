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

// REPEAT 7 - TIME: 75.6912949 s
