method {:testEntry} CountCharacters(s: string) returns (count: int)
    ensures count >= 0
    ensures count == |s|
{
    count := |s|;
}

method {:test} Test6() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 7 - TIME: 8.6148644 s
