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

method {:test} Test40() {
var r0 := CountVowelNeighbors("a\0a\U{0001}aaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test41() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}aaa\0aaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test42() {
var r0 := CountVowelNeighbors("a\U{0001}a\U{0002}aa\0aaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 81.490874 s
