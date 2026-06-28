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
