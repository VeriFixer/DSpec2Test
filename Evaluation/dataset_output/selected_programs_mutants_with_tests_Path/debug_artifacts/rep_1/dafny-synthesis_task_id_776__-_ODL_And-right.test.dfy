// dafny-synthesis_task_id_776.dfy

predicate IsVowel(c: char)
{
  c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

method {:testEntry} CountVowelNeighbors(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 1 <= i < |s| - 1 && IsVowel(s[i - 1]) && IsVowel(s[i + 1])|
{
  var vowels := set i: int | 1 <= i < |s| - 1;
  count := |vowels|;
}

method {:test} Test0() {
var r0 := CountVowelNeighbors("aaaaaaaaOaOaaaaaaaaUaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test1() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaaaaIa\0aaaaaa");
expect r0 >= 0;
}
method {:test} Test2() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa");
expect r0 >= 0;
}
method {:test} Test3() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaUaO");
expect r0 >= 0;
}
method {:test} Test4() {
var r0 := CountVowelNeighbors("aaaaaaaaaaaaaaaaaaaoaIaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 9.3708982 s
