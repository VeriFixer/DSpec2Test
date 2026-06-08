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
var r0 := CountVowelNeighbors("\naaaaaa\U{0006}\U{0004}aaaaaaaaaaaa\U{0002}aaaaaaaaaa\0a\U{0008}");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 12.1458653 s
