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

method {:test} Test45() {
var r0 := CountVowelNeighbors("\U{0005}\0a\U{0001}aaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test46() {
var r0 := CountVowelNeighbors("a\U{0001}aaaaaaa\0aaaaaaa");
expect r0 >= 0;
}
method {:test} Test47() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}aaaaaaaaa\0aaa");
expect r0 >= 0;
}
method {:test} Test48() {
var r0 := CountVowelNeighbors("a\0aaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test49() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 96.3406402 s
