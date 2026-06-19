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

method {:test} Test10() {
var r0 := CountVowelNeighbors("eaa");
expect r0 >= 0;
}
method {:test} Test11() {
var r0 := CountVowelNeighbors("a\U{0001}aaaaaaaaaa\0aaaaaaa\U{0005}aa\U{0007}\t\U{000B}\U{0003}");
expect r0 >= 0;
}
method {:test} Test12() {
var r0 := CountVowelNeighbors("\U{000B}\U{000C}\U{0002}\U{0001}\n\t\U{0008}\U{0007}\0\U{0006}\U{0005}\U{0004}\U{0003}");
expect r0 >= 0;
}
method {:test} Test13() {
var r0 := CountVowelNeighbors("a\0aaaaaaaaaaaaaaaa\U{0002}a\U{0004}aa\U{0006}a\U{0008}a");
expect r0 >= 0;
}
method {:test} Test14() {
var r0 := CountVowelNeighbors("\U{0004}\0a\U{0001}aaaaa\U{0002}a");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 13.560099 s
