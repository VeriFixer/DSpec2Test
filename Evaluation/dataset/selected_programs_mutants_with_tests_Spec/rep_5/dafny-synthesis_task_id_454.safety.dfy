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

method {:test} Test12() {
var r0 := ContainsZ("\U{0005}aaaaaa\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaza");
expect r0 <==> exists i :: 0 <= i < |"\U{0005}aaaaaa\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaza"| && ("\U{0005}aaaaaa\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaza"[i] == 'z' || "\U{0005}aaaaaa\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaza"[i] == 'Z');
}
method {:test} Test13() {
var r0 := ContainsZ("\U{0003}\U{0001}Z");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}\U{0001}Z"| && ("\U{0003}\U{0001}Z"[i] == 'z' || "\U{0003}\U{0001}Z"[i] == 'Z');
}
method {:test} Test14() {
var r0 := ContainsZ("\U{0008}aa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaa\U{0004}\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\U{0008}aa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaa\U{0004}\U{0006}"| && ("\U{0008}aa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaa\U{0004}\U{0006}"[i] == 'z' || "\U{0008}aa\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aaa\U{0004}\U{0006}"[i] == 'Z');
}

// REPEAT 5 - TIME: 10.0638436 s
