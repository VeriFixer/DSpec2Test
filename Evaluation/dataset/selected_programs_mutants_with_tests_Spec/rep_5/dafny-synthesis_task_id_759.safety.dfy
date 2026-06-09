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

method {:test} Test8() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}a\0aaaaaaaaaaa\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}a\0aaaaaaaaaaa\U{0002}"| && "\U{0004}a\0aaaaaaaaaaa\U{0002}"[i] == '.' && |"\U{0004}a\0aaaaaaaaaaa\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}a\0aaaaaaaaaaa\U{0002}"| && "\U{0004}a\0aaaaaaaaaaa\U{0002}"[i] == '.' && |"\U{0004}a\0aaaaaaaaaaa\U{0002}"| - i - 1 == 2;
}
method {:test} Test9() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\U{0004}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\U{0004}"| && "aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\U{0004}"[i] == '.' && |"aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\U{0004}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\U{0004}"| && "aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\U{0004}"[i] == '.' && |"aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\U{0004}"| - i - 1 == 2;
}

// REPEAT 5 - TIME: 7.9836307 s
