method {:testEntry} IsDecimalWithTwoPrecision(s: string) returns (result: bool)
    ensures result ==> (exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
    ensures !result ==> !(exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
{
    result := false;
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant result <==> (exists k :: 0 <= k < i && s[k] == '.' && |s| - k - 1 == 2)
    {
        if s[i] == '.' && |s| - i - 1 == 2 {
            result := true;
            break;
        }
    }
}

method {:test} Test14() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}\0\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}\0\U{0002}"| && "\U{0004}\0\U{0002}"[i] == '.' && |"\U{0004}\0\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}\0\U{0002}"| && "\U{0004}\0\U{0002}"[i] == '.' && |"\U{0004}\0\U{0002}"| - i - 1 == 2;
}
method {:test} Test15() {
var r0 := IsDecimalWithTwoPrecision("\U{0005}aa.\U{0001}\U{0003}");
expect r0 ==> exists i :: 0 <= i < |"\U{0005}aa.\U{0001}\U{0003}"| && "\U{0005}aa.\U{0001}\U{0003}"[i] == '.' && |"\U{0005}aa.\U{0001}\U{0003}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0005}aa.\U{0001}\U{0003}"| && "\U{0005}aa.\U{0001}\U{0003}"[i] == '.' && |"\U{0005}aa.\U{0001}\U{0003}"| - i - 1 == 2;
}

// REPEAT 8 - TIME: 11.5912539 s
