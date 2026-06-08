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

method {:test} Test35() {
var r0 := CountVowelNeighbors("a\U{0001}a");
expect r0 >= 0;
}
method {:test} Test36() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}aaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test37() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaaa");
expect r0 >= 0;
}
method {:test} Test38() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test39() {
var r0 := CountVowelNeighbors("a\0a\U{0001}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 92.7547095 s
