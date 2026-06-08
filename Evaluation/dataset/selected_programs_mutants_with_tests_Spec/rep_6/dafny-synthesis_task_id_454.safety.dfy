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
var r0 := ContainsZ("\taa\U{0001}aaaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}za\U{0007}");
expect r0 <==> exists i :: 0 <= i < |"\taa\U{0001}aaaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}za\U{0007}"| && ("\taa\U{0001}aaaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}za\U{0007}"[i] == 'z' || "\taa\U{0001}aaaa\U{0005}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}za\U{0007}"[i] == 'Z');
}
method {:test} Test16() {
var r0 := ContainsZ("Z");
expect r0 <==> exists i :: 0 <= i < |"Z"| && ("Z"[i] == 'z' || "Z"[i] == 'Z');
}
method {:test} Test17() {
var r0 := ContainsZ("\U{0004}a\U{0002}\0");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}a\U{0002}\0"| && ("\U{0004}a\U{0002}\0"[i] == 'z' || "\U{0004}a\U{0002}\0"[i] == 'Z');
}

// REPEAT 6 - TIME: 13.7423978 s
