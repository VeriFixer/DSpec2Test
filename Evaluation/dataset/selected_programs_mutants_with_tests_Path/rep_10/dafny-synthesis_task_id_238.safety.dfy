method {:testEntry} CountNonEmptySubstrings(s: string) returns (count: int)
    ensures count >= 0
    ensures count == (|s| * (|s| + 1)) / 2 // Formula for the number of non-empty substrings of a string
{
    count := (|s| * (|s| + 1)) / 2;
}

method {:test} Test9() {
var r0 := CountNonEmptySubstrings("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"| * (|"\U{0002}\0"| + 1) / 2;
}

// REPEAT 10 - TIME: 11.5092803 s
