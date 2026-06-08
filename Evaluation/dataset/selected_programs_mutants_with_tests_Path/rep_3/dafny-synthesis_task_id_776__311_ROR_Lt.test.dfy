// dafny-synthesis_task_id_776.dfy

predicate IsVowel(c: char)
{
  c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

method {:testEntry} CountVowelNeighbors(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 1 <= i < |s| - 1 && IsVowel(s[i - 1]) && IsVowel(s[i + 1])|
{
  var vowels := set i: int | 1 < i < |s| - 1 && IsVowel(s[i - 1]) && IsVowel(s[i + 1]);
  count := |vowels|;
}

method {:test} Test10() {
var r0 := CountVowelNeighbors("\U{0006}a\U{0008}aaaaaaaaaaaaa\0aaaaaaaaaaaaaa\U{0002}a");
expect r0 >= 0;
}
method {:test} Test11() {
var r0 := CountVowelNeighbors("aaa\U{0011}aaaaaaaaaaaa\U{0003}\U{0005}aaaaaaaaaaaa\0\U{0007}\raaaa\taaaa\U{000B}\U{000F}");
expect r0 >= 0;
}
method {:test} Test12() {
var r0 := CountVowelNeighbors("\U{0017}\U{0019}\U{001B}aaaaaaa\0a\U{0001}\U{0013}\U{0002}");
expect r0 >= 0;
}
method {:test} Test13() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaa\U{0001}\U{0003}aaaaaaaaaaaaa\U{0005}\U{000B}aaa\U{0007}aaaaaa\ra\U{000F}\taa\U{0011}");
expect r0 >= 0;
}
method {:test} Test14() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaa\U{0001}\U{0003}aaaaaaaaaaaaa\U{0005}aaaa\U{0007}aaaaaa\U{000B}a\r\taa\U{000F}");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 27.7928439 s
