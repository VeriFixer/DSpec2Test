// dafny-synthesis_task_id_776.dfy

predicate IsVowel(c: char)
{
  c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

method {:testEntry} CountVowelNeighbors(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 1 <= i < |s| - 1 && IsVowel(s[i - 1]) && IsVowel(s[i + 1])|
{
  var vowels := set i: int | 1 <= i < |s| - 1 && IsVowel(s[i]) && IsVowel(s[i + 1]);
  count := |vowels|;
}

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

// REPEAT 7 - TIME: 56.1676012 s
