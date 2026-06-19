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

method {:test} Test25() {
var r0 := CountVowelNeighbors("\U{0004}\0a\U{0001}aaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test26() {
var r0 := CountVowelNeighbors("\U{0006}\U{0001}a\U{0002}aaaaaaaaaaaaaaaa\0a");
expect r0 >= 0;
}
method {:test} Test27() {
var r0 := CountVowelNeighbors("\U{0006}\U{0001}a\U{0002}aaaaaaaaaaaaaaa\0aa");
expect r0 >= 0;
}
method {:test} Test29() {
var r0 := CountVowelNeighbors("\0aaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 29.5662498 s
