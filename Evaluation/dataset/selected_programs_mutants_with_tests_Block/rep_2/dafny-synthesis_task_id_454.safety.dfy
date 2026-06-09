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

method {:test} Test2() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaZaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaZaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| && ("aaaaaaaaaaaaaaaaaZaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] == 'z' || "aaaaaaaaaaaaaaaaaZaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] == 'Z');
}
method {:test} Test3() {
var r0 := ContainsZ("aaaaaz");
expect r0 <==> exists i :: 0 <= i < |"aaaaaz"| && ("aaaaaz"[i] == 'z' || "aaaaaz"[i] == 'Z');
}

// REPEAT 2 - TIME: 4.169998 s
