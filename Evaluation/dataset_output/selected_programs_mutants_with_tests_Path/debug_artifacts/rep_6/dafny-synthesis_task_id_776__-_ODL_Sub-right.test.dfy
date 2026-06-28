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
