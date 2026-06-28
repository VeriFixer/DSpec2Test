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
