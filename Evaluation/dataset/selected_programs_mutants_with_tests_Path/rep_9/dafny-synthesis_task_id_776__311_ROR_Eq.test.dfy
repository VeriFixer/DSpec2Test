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

method {:test} Test40() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa");
expect r0 >= 0;
}
method {:test} Test41() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0005}\0aaa");
expect r0 >= 0;
}
method {:test} Test42() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test43() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test44() {
var r0 := CountVowelNeighbors("a\0a\U{0001}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 72.7980228 s
