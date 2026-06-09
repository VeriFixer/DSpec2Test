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

method {:test} Test22() {
var r0 := IsDecimalWithTwoPrecision("a\U{000E}aaaaaaa\U{0004}aa\U{0006}aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0008}\U{000C}\0\n");
expect r0 ==> exists i :: 0 <= i < |"a\U{000E}aaaaaaa\U{0004}aa\U{0006}aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0008}\U{000C}\0\n"| && "a\U{000E}aaaaaaa\U{0004}aa\U{0006}aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0008}\U{000C}\0\n"[i] == '.' && |"a\U{000E}aaaaaaa\U{0004}aa\U{0006}aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0008}\U{000C}\0\n"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"a\U{000E}aaaaaaa\U{0004}aa\U{0006}aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0008}\U{000C}\0\n"| && "a\U{000E}aaaaaaa\U{0004}aa\U{0006}aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0008}\U{000C}\0\n"[i] == '.' && |"a\U{000E}aaaaaaa\U{0004}aa\U{0006}aaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaaa\U{0008}\U{000C}\0\n"| - i - 1 == 2;
}
method {:test} Test23() {
var r0 := IsDecimalWithTwoPrecision("aa\U{0001}aaaaaa\U{0005}aa\U{0007}\taaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaa\U{000B}a.aa");
expect r0 ==> exists i :: 0 <= i < |"aa\U{0001}aaaaaa\U{0005}aa\U{0007}\taaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaa\U{000B}a.aa"| && "aa\U{0001}aaaaaa\U{0005}aa\U{0007}\taaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaa\U{000B}a.aa"[i] == '.' && |"aa\U{0001}aaaaaa\U{0005}aa\U{0007}\taaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaa\U{000B}a.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aa\U{0001}aaaaaa\U{0005}aa\U{0007}\taaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaa\U{000B}a.aa"| && "aa\U{0001}aaaaaa\U{0005}aa\U{0007}\taaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaa\U{000B}a.aa"[i] == '.' && |"aa\U{0001}aaaaaa\U{0005}aa\U{0007}\taaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaa\U{000B}a.aa"| - i - 1 == 2;
}

// REPEAT 6 - TIME: 14.2240997 s
