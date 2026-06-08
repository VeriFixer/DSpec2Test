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

method {:test} Test9() {
var r0 := ContainsZ("\U{0003}\U{0001}z");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}\U{0001}z"| && ("\U{0003}\U{0001}z"[i] == 'z' || "\U{0003}\U{0001}z"[i] == 'Z');
}
method {:test} Test10() {
var r0 := ContainsZ("\U{0005}aa\U{0001}aaaaaaaaaaaaaaaaaaaa\U{0003}aaaaaaaaaaaaaZaa");
expect r0 <==> exists i :: 0 <= i < |"\U{0005}aa\U{0001}aaaaaaaaaaaaaaaaaaaa\U{0003}aaaaaaaaaaaaaZaa"| && ("\U{0005}aa\U{0001}aaaaaaaaaaaaaaaaaaaa\U{0003}aaaaaaaaaaaaaZaa"[i] == 'z' || "\U{0005}aa\U{0001}aaaaaaaaaaaaaaaaaaaa\U{0003}aaaaaaaaaaaaaZaa"[i] == 'Z');
}
method {:test} Test11() {
var r0 := ContainsZ("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a");
expect r0 <==> exists i :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a"| && ("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a"[i] == 'z' || "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a"[i] == 'Z');
}

// REPEAT 4 - TIME: 9.7421231 s
