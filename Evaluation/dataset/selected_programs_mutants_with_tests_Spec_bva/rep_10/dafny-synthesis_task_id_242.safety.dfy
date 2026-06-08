method {:testEntry} CountCharacters(s: string) returns (count: int)
    ensures count >= 0
    ensures count == |s|
{
    count := |s|;
}

method {:test} Test16() {
var r0 := CountCharacters("\0\U{0002}");
expect r0 >= 0;
expect r0 == |"\0\U{0002}"|;
}

// REPEAT 10 - TIME: 14.0193318 s
