method {:testEntry} CountCharacters(s: string) returns (count: int)
    ensures count >= 0
    ensures count == |s|
{
    count := |s|;
}

method {:test} Test12() {
var r0 := CountCharacters("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}");
expect r0 >= 0;
expect r0 == |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}"|;
}

// REPEAT 6 - TIME: 9.9322968 s
