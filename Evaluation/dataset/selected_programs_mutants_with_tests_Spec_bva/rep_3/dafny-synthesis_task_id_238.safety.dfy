method {:testEntry} CountNonEmptySubstrings(s: string) returns (count: int)
    ensures count >= 0
    ensures count == (|s| * (|s| + 1)) / 2 // Formula for the number of non-empty substrings of a string
{
    count := (|s| * (|s| + 1)) / 2;
}

method {:test} Test9() {
var r0 := CountNonEmptySubstrings("aa\0\U{0002}");
expect r0 >= 0;
expect r0 == |"aa\0\U{0002}"| * (|"aa\0\U{0002}"| + 1) / 2;
}

// REPEAT 3 - TIME: 7.6843643 s
