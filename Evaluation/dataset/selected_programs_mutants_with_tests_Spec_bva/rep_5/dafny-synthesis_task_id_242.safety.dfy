method {:testEntry} CountCharacters(s: string) returns (count: int)
    ensures count >= 0
    ensures count == |s|
{
    count := |s|;
}

method {:test} Test11() {
var r0 := CountCharacters("\0");
expect r0 >= 0;
expect r0 == |"\0"|;
}

// REPEAT 5 - TIME: 9.8213424 s
