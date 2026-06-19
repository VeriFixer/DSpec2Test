// dafny-synthesis_task_id_776.dfy

predicate IsVowel(c: char)
{
  c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

method {:testEntry} CountVowelNeighbors(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 1 <= i < |s| - 1 && IsVowel(s[i - 1]) && IsVowel(s[i + 1])|
{
}

method {:test} Test15() {
var r0 := CountVowelNeighbors("\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test16() {
var r0 := CountVowelNeighbors("\U{0005}\U{0001}a\U{0002}aaaaaaa\0aaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test17() {
var r0 := CountVowelNeighbors("\U{0005}\U{0001}a\U{0002}aaaaaaaaaaaaaaa\0aaaaaaa");
expect r0 >= 0;
}
method {:test} Test18() {
var r0 := CountVowelNeighbors("\U{0004}\0a\U{0001}aaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test19() {
var r0 := CountVowelNeighbors("\U{0006}\0a\U{0001}aaaaaa\U{0002}\U{0004}");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 18.5115714 s
