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

method {:test} Test6() {
var r0 := CountVowelNeighbors("\U{0008}\0aaaaaa\U{0006}a\U{0004}aaaaaaaa\U{0002}aaaaaaaaa\n");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 8.9005487 s
