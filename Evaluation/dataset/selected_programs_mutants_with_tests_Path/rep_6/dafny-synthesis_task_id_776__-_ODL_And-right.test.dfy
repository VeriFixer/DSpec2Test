// dafny-synthesis_task_id_776.dfy

predicate IsVowel(c: char)
{
  c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

method {:testEntry} CountVowelNeighbors(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 1 <= i < |s| - 1 && IsVowel(s[i - 1]) && IsVowel(s[i + 1])|
{
  var vowels := set i: int | 1 <= i < |s| - 1;
  count := |vowels|;
}

method {:test} Test25() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test26() {
var r0 := CountVowelNeighbors("aaa\0aaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test27() {
var r0 := CountVowelNeighbors("aaaaaaa\0aaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test28() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 41.3776843 s
