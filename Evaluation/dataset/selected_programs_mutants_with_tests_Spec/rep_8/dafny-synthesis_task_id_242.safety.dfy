method {:testEntry} CountCharacters(s: string) returns (count: int)
    ensures count >= 0
    ensures count == |s|
{
    count := |s|;
}

method {:test} Test7() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 8 - TIME: 9.6437032 s
