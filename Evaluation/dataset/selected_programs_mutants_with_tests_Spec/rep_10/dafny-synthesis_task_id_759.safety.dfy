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
var r0 := IsDecimalWithTwoPrecision("\U{0014}aaaaaa\U{0002}aaaaaaa\U{0010}a\U{0004}aaa\U{000C}\U{0006}aaaaaaaaaaaaaa\U{000E}\n\U{0008}\0\U{0012}");
expect r0 ==> exists i :: 0 <= i < |"\U{0014}aaaaaa\U{0002}aaaaaaa\U{0010}a\U{0004}aaa\U{000C}\U{0006}aaaaaaaaaaaaaa\U{000E}\n\U{0008}\0\U{0012}"| && "\U{0014}aaaaaa\U{0002}aaaaaaa\U{0010}a\U{0004}aaa\U{000C}\U{0006}aaaaaaaaaaaaaa\U{000E}\n\U{0008}\0\U{0012}"[i] == '.' && |"\U{0014}aaaaaa\U{0002}aaaaaaa\U{0010}a\U{0004}aaa\U{000C}\U{0006}aaaaaaaaaaaaaa\U{000E}\n\U{0008}\0\U{0012}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0014}aaaaaa\U{0002}aaaaaaa\U{0010}a\U{0004}aaa\U{000C}\U{0006}aaaaaaaaaaaaaa\U{000E}\n\U{0008}\0\U{0012}"| && "\U{0014}aaaaaa\U{0002}aaaaaaa\U{0010}a\U{0004}aaa\U{000C}\U{0006}aaaaaaaaaaaaaa\U{000E}\n\U{0008}\0\U{0012}"[i] == '.' && |"\U{0014}aaaaaa\U{0002}aaaaaaa\U{0010}a\U{0004}aaa\U{000C}\U{0006}aaaaaaaaaaaaaa\U{000E}\n\U{0008}\0\U{0012}"| - i - 1 == 2;
}
method {:test} Test19() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}\0a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}\0a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "\U{0002}\0a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"\U{0002}\0a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}\0a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "\U{0002}\0a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"\U{0002}\0a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
}

// REPEAT 10 - TIME: 16.0637551 s
