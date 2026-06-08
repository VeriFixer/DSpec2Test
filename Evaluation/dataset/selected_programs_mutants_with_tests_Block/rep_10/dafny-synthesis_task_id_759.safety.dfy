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

method {:test} Test18() {
var r0 := IsDecimalWithTwoPrecision("\U{0007}aaaaaaaaaaaaaaa\U{0001}a\U{0005}aaaaaa\U{0003}.aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0007}aaaaaaaaaaaaaaa\U{0001}a\U{0005}aaaaaa\U{0003}.aa"| && "\U{0007}aaaaaaaaaaaaaaa\U{0001}a\U{0005}aaaaaa\U{0003}.aa"[i] == '.' && |"\U{0007}aaaaaaaaaaaaaaa\U{0001}a\U{0005}aaaaaa\U{0003}.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0007}aaaaaaaaaaaaaaa\U{0001}a\U{0005}aaaaaa\U{0003}.aa"| && "\U{0007}aaaaaaaaaaaaaaa\U{0001}a\U{0005}aaaaaa\U{0003}.aa"[i] == '.' && |"\U{0007}aaaaaaaaaaaaaaa\U{0001}a\U{0005}aaaaaa\U{0003}.aa"| - i - 1 == 2;
}
method {:test} Test19() {
var r0 := IsDecimalWithTwoPrecision("\0\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\0\U{0002}"| && "\0\U{0002}"[i] == '.' && |"\0\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0\U{0002}"| && "\0\U{0002}"[i] == '.' && |"\0\U{0002}"| - i - 1 == 2;
}

// REPEAT 10 - TIME: 17.3217025 s
