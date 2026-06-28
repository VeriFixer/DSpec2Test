// dafny-synthesis_task_id_776.dfy

predicate IsVowel(c: char)
{
  c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

method {:testEntry} CountVowelNeighbors(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 1 <= i < |s| - 1 && IsVowel(s[i - 1]) && IsVowel(s[i + 1])|
{
  var vowels := set i: int | 1 <= i < |s| - 1 && IsVowel(s[i]) && IsVowel(s[i + 1]);
  count := |vowels|;
}

method {:test} Test11() {
var r0 := CountVowelNeighbors("\U{0006}\0aaaaaa\U{0002}aaaaaaaaaaaaaaaaaaa\U{0004}");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 12.4562182 s
