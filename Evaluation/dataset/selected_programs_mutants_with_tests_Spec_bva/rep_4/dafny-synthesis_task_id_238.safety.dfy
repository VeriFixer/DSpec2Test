method {:testEntry} CountNonEmptySubstrings(s: string) returns (count: int)
    ensures count >= 0
    ensures count == (|s| * (|s| + 1)) / 2 // Formula for the number of non-empty substrings of a string
{
    count := (|s| * (|s| + 1)) / 2;
}

method {:test} Test10() {
var r0 := CountNonEmptySubstrings("\0a");
expect r0 >= 0;
expect r0 == |"\0a"| * (|"\0a"| + 1) / 2;
}

// REPEAT 4 - TIME: 8.2949007 s
