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
