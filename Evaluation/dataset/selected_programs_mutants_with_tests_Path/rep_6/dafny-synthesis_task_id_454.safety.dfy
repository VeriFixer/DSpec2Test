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

method {:test} Test15() {
var r0 := ContainsZ("\U{0006}aaaaaaaaaaaa\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaa\U{0008}a\na\U{0004}aaaa\U{000C}");
expect r0 <==> exists i :: 0 <= i < |"\U{0006}aaaaaaaaaaaa\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaa\U{0008}a\na\U{0004}aaaa\U{000C}"| && ("\U{0006}aaaaaaaaaaaa\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaa\U{0008}a\na\U{0004}aaaa\U{000C}"[i] == 'z' || "\U{0006}aaaaaaaaaaaa\U{0002}aaaaaaaaaa\0aaaaaaaaaaaaaa\U{0008}a\na\U{0004}aaaa\U{000C}"[i] == 'Z');
}
method {:test} Test16() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz"[i] == 'Z');
}
method {:test} Test17() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}Z");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}Z"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}Z"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}Z"[i] == 'Z');
}

// REPEAT 6 - TIME: 276.0127737 s
