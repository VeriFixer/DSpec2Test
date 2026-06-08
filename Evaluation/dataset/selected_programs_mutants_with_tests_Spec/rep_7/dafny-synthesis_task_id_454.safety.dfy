method {:testEntry} ContainsZ(s: string) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z'))
{
    result := false;
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant result <==> (exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z'))
    {
        if s[i] == 'z' || s[i] == 'Z' {
            result := true;
            break;
        }
    }
}

method {:test} Test18() {
var r0 := ContainsZ("\U{0005}aaaaa\taaaaaaaaaaaaaaaaaaaaa\U{0007}aaaa\U{0003}aaa\U{0001}z");
expect r0 <==> exists i :: 0 <= i < |"\U{0005}aaaaa\taaaaaaaaaaaaaaaaaaaaa\U{0007}aaaa\U{0003}aaa\U{0001}z"| && ("\U{0005}aaaaa\taaaaaaaaaaaaaaaaaaaaa\U{0007}aaaa\U{0003}aaa\U{0001}z"[i] == 'z' || "\U{0005}aaaaa\taaaaaaaaaaaaaaaaaaaaa\U{0007}aaaa\U{0003}aaa\U{0001}z"[i] == 'Z');
}
method {:test} Test19() {
var r0 := ContainsZ("\U{0008}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaa\0\U{0002}aa\U{0006}Z");
expect r0 <==> exists i :: 0 <= i < |"\U{0008}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaa\0\U{0002}aa\U{0006}Z"| && ("\U{0008}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaa\0\U{0002}aa\U{0006}Z"[i] == 'z' || "\U{0008}aaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaa\0\U{0002}aa\U{0006}Z"[i] == 'Z');
}
method {:test} Test20() {
var r0 := ContainsZ("\U{000E}a\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\0aaaaaaa\U{0008}\n\U{000C}");
expect r0 <==> exists i :: 0 <= i < |"\U{000E}a\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\0aaaaaaa\U{0008}\n\U{000C}"| && ("\U{000E}a\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\0aaaaaaa\U{0008}\n\U{000C}"[i] == 'z' || "\U{000E}a\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaaa\U{0006}aaaaa\0aaaaaaa\U{0008}\n\U{000C}"[i] == 'Z');
}

// REPEAT 7 - TIME: 15.6719385 s
