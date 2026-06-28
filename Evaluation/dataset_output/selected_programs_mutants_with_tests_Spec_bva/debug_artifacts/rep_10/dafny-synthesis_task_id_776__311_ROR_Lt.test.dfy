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

method {:test} Test17() {
var r0 := CountVowelNeighbors("\U{0010}\0a\U{0001}aaaaa\U{0008}a\U{000C}aaaaaaa\U{0006}aaaaaa\U{0002}\n\U{0003}a");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 18.8684194 s
