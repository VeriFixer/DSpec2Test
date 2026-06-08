method {:testEntry} CountCharacters(s: string) returns (count: int)
    ensures count >= 0
    ensures count == |s|
{
    count := |s|;
}

method {:test} Test15() {
var r0 := CountCharacters("\0");
expect r0 >= 0;
expect r0 == |"\0"|;
}

// REPEAT 9 - TIME: 13.1660483 s
