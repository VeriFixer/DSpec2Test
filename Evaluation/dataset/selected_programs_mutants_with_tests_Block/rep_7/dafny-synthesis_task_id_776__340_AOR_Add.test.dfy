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

method {:test} Test6() {
var r0 := CountVowelNeighbors("\0aaa");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 7.477501 s
