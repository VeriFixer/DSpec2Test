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

method {:test} Test16() {
var r0 := CountVowelNeighbors("\na\0\U{0004}a\U{0006}\U{0002}\U{0008}");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 11.661129 s
