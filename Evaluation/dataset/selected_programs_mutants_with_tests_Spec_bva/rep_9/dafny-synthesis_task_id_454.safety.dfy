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

method {:test} Test43() {
var r0 := ContainsZ("\U{000F}aaaa\raaa\U{0001}aaaaaaaaaaaaaa\U{0005}\U{0007}a\taaaaaaaaaazaa\U{000B}a\U{0003}aaaaaa");
expect r0 <==> exists i :: 0 <= i < |"\U{000F}aaaa\raaa\U{0001}aaaaaaaaaaaaaa\U{0005}\U{0007}a\taaaaaaaaaazaa\U{000B}a\U{0003}aaaaaa"| && ("\U{000F}aaaa\raaa\U{0001}aaaaaaaaaaaaaa\U{0005}\U{0007}a\taaaaaaaaaazaa\U{000B}a\U{0003}aaaaaa"[i] == 'z' || "\U{000F}aaaa\raaa\U{0001}aaaaaaaaaaaaaa\U{0005}\U{0007}a\taaaaaaaaaazaa\U{000B}a\U{0003}aaaaaa"[i] == 'Z');
}
method {:test} Test44() {
var r0 := ContainsZ("aa\taaaaaaaaaaaaaaaaaaaaa\U{0005}a\U{0001}aaaaaaaaaaaZaa\U{0007}aaaa\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"aa\taaaaaaaaaaaaaaaaaaaaa\U{0005}a\U{0001}aaaaaaaaaaaZaa\U{0007}aaaa\U{0003}"| && ("aa\taaaaaaaaaaaaaaaaaaaaa\U{0005}a\U{0001}aaaaaaaaaaaZaa\U{0007}aaaa\U{0003}"[i] == 'z' || "aa\taaaaaaaaaaaaaaaaaaaaa\U{0005}a\U{0001}aaaaaaaaaaaZaa\U{0007}aaaa\U{0003}"[i] == 'Z');
}
method {:test} Test45() {
var r0 := ContainsZ("aaa\n\U{0008}aaaaaaaaaaaaaaaaaaaaa\0\U{0002}aaaaaaaaaa\U{0004}aaa\U{0006}aaaa");
expect r0 <==> exists i :: 0 <= i < |"aaa\n\U{0008}aaaaaaaaaaaaaaaaaaaaa\0\U{0002}aaaaaaaaaa\U{0004}aaa\U{0006}aaaa"| && ("aaa\n\U{0008}aaaaaaaaaaaaaaaaaaaaa\0\U{0002}aaaaaaaaaa\U{0004}aaa\U{0006}aaaa"[i] == 'z' || "aaa\n\U{0008}aaaaaaaaaaaaaaaaaaaaa\0\U{0002}aaaaaaaaaa\U{0004}aaa\U{0006}aaaa"[i] == 'Z');
}

// REPEAT 9 - TIME: 28.0172353 s
