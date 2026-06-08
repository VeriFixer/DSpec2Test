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

method {:test} Test26() {
var r0 := IsDecimalWithTwoPrecision("aaaaa\U{0018}aaaaaaa\U{0008}\0aaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\U{0004}a\U{000C}\U{000E}\U{0010}\U{0012}\n\U{0002}\U{0014}\U{0016}");
expect r0 ==> exists i :: 0 <= i < |"aaaaa\U{0018}aaaaaaa\U{0008}\0aaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\U{0004}a\U{000C}\U{000E}\U{0010}\U{0012}\n\U{0002}\U{0014}\U{0016}"| && "aaaaa\U{0018}aaaaaaa\U{0008}\0aaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\U{0004}a\U{000C}\U{000E}\U{0010}\U{0012}\n\U{0002}\U{0014}\U{0016}"[i] == '.' && |"aaaaa\U{0018}aaaaaaa\U{0008}\0aaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\U{0004}a\U{000C}\U{000E}\U{0010}\U{0012}\n\U{0002}\U{0014}\U{0016}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaa\U{0018}aaaaaaa\U{0008}\0aaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\U{0004}a\U{000C}\U{000E}\U{0010}\U{0012}\n\U{0002}\U{0014}\U{0016}"| && "aaaaa\U{0018}aaaaaaa\U{0008}\0aaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\U{0004}a\U{000C}\U{000E}\U{0010}\U{0012}\n\U{0002}\U{0014}\U{0016}"[i] == '.' && |"aaaaa\U{0018}aaaaaaa\U{0008}\0aaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\U{0004}a\U{000C}\U{000E}\U{0010}\U{0012}\n\U{0002}\U{0014}\U{0016}"| - i - 1 == 2;
}
method {:test} Test27() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}.\U{0001}\U{0005}");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}.\U{0001}\U{0005}"| && "\U{0003}.\U{0001}\U{0005}"[i] == '.' && |"\U{0003}.\U{0001}\U{0005}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}.\U{0001}\U{0005}"| && "\U{0003}.\U{0001}\U{0005}"[i] == '.' && |"\U{0003}.\U{0001}\U{0005}"| - i - 1 == 2;
}

// REPEAT 8 - TIME: 17.5564168 s
