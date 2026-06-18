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


predicate IsVowel(c: char)
{
    c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

method {:testEntry} CountVowelNeighbors(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
{
    var vowels := set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]);
    count := |vowels|;
}

method {:test} Test0() {
var r0 := CountVowelNeighbors("aaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 2.504379 s

method {:test} Test1() {
var r0 := CountVowelNeighbors("aaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 3.6399528 s

method {:test} Test2() {
var r0 := CountVowelNeighbors("\0a");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 4.5472105 s

method {:test} Test3() {
var r0 := CountVowelNeighbors("\0aaaaaaaaaaaaaaa\U{0002}aa");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 5.4236417 s

method {:test} Test4() {
var r0 := CountVowelNeighbors("\0");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 6.2654792 s

method {:test} Test5() {
var r0 := CountVowelNeighbors("\U{0004}aaaaaaaa\U{0002}aaaaaaaa\0a");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 7.0866207 s

method {:test} Test6() {
var r0 := CountVowelNeighbors("\U{0002}\0");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 8.000944 s

method {:test} Test7() {
var r0 := CountVowelNeighbors("\U{0004}aa\0aaa\U{0002}aaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 8.7317466 s

method {:test} Test8() {
var r0 := CountVowelNeighbors("\U{0002}aaaaaaa\0aaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 9.5935438 s

method {:test} Test9() {
var r0 := CountVowelNeighbors("\U{0006}\0aaaaa\U{0002}a\U{0004}aaaaaaaa\U{0008}\naaaaaaa\U{000E}\U{000C}");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 10.3081655 s
