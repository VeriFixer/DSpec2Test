method {:testEntry} CountCharacters(s: string) returns (count: int)
    ensures count >= 0
    ensures count == |s|
{
    count := |s|;
}

method {:test} Test4() {
var r0 := CountCharacters("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
expect r0 == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|;
}

// REPEAT 5 - TIME: 6.7610987 s
