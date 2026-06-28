// dafny-synthesis_task_id_776.dfy

predicate IsVowel(c: char)
{
  c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

method {:testEntry} CountVowelNeighbors(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 1 <= i < |s| - 1 && IsVowel(s[i - 1]) && IsVowel(s[i + 1])|
{
  var vowels := set i: int | 1 <= i < |s| - 1 && IsVowel(s[i + 1]) && IsVowel(s[i + 1]);
  count := |vowels|;
}

method {:test} Test14() {
var r0 := CountVowelNeighbors("\n\0a\U{0003}aaaaa\U{0007}\U{0001}\U{0005}");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 15.9573315 s
