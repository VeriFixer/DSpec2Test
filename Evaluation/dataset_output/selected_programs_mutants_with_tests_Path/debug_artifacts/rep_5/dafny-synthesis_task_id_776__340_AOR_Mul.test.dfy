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

method {:test} Test20() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test21() {
var r0 := CountVowelNeighbors("a\U{0001}aaaaaaaaaaaaaa\0aa\U{0005}aaa\U{0003}aaa\U{000B}\U{0007}\t");
expect r0 >= 0;
}
method {:test} Test22() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}aaaaaaaaaaaaaaa\0aaaaa\U{0007}a\t\U{0005}a");
expect r0 >= 0;
}
method {:test} Test23() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaa\U{0004}aaaaaaaaaaaa\U{0006}\U{0008}a");
expect r0 >= 0;
}
method {:test} Test24() {
var r0 := CountVowelNeighbors("a\0aaaaaaaaaaaaaa\U{0003}aaaaaa\U{0001}aaa\U{0005}\U{0007}a");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 29.5996872 s
