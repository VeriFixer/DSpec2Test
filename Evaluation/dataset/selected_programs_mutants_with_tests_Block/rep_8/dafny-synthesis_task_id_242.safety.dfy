method {:testEntry} CountCharacters(s: string) returns (count: int)
    ensures count >= 0
    ensures count == |s|
{
    count := |s|;
}

method {:test} Test7() {
var r0 := CountCharacters("a\0aaaaa\U{0002}aaaaaaa\U{0004}");
expect r0 >= 0;
expect r0 == |"a\0aaaaa\U{0002}aaaaaaa\U{0004}"|;
}

// REPEAT 8 - TIME: 6.8004222 s
