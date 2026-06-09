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

method {:test} Test3() {
var r0 := ContainsZ("z");
expect r0 <==> exists i :: 0 <= i < |"z"| && ("z"[i] == 'z' || "z"[i] == 'Z');
}
method {:test} Test4() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\U{0001}"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\U{0001}"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ\U{0001}"[i] == 'Z');
}
method {:test} Test5() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] == 'Z');
}

// REPEAT 2 - TIME: 4.9797872 s
