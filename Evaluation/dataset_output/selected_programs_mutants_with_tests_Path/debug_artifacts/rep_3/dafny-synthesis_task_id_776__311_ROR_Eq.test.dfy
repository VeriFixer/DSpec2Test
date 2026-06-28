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

method {:test} Test10() {
var r0 := CountVowelNeighbors("\U{000E}aaaaaaaaaaaaaaaaaa\0aaa\U{0002}\U{0004}\U{0006}\n\U{0008}a\U{000C}");
expect r0 >= 0;
}
method {:test} Test11() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaa\0aa\U{0002}aaa\U{0004}\U{0006}\U{0008}\n\U{000C}\U{0010}\U{000E}");
expect r0 >= 0;
}
method {:test} Test12() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaa\0aaa\U{0005}\U{0007}\t\U{0003}\U{000B}\r\U{000F}");
expect r0 >= 0;
}
method {:test} Test13() {
var r0 := CountVowelNeighbors("\0aa");
expect r0 >= 0;
}
method {:test} Test14() {
var r0 := CountVowelNeighbors("eaa");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 23.3319876 s
