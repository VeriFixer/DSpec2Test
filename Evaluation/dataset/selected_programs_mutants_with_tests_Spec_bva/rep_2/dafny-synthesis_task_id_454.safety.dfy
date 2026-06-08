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

method {:test} Test22() {
var r0 := ContainsZ("a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz\U{0005}aaaaaaa\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz\U{0005}aaaaaaa\U{0003}"| && ("a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz\U{0005}aaaaaaa\U{0003}"[i] == 'z' || "a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz\U{0005}aaaaaaa\U{0003}"[i] == 'Z');
}
method {:test} Test23() {
var r0 := ContainsZ("\U{0003}\U{0001}Z");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}\U{0001}Z"| && ("\U{0003}\U{0001}Z"[i] == 'z' || "\U{0003}\U{0001}Z"[i] == 'Z');
}
method {:test} Test24() {
var r0 := ContainsZ("\U{0004}\0\U{0002}");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}\0\U{0002}"| && ("\U{0004}\0\U{0002}"[i] == 'z' || "\U{0004}\0\U{0002}"[i] == 'Z');
}

// REPEAT 2 - TIME: 14.0912405 s
