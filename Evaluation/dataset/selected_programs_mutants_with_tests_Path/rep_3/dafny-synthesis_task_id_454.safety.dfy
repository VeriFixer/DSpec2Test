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

method {:test} Test6() {
var r0 := ContainsZ("\U{0002}\0");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}\0"| && ("\U{0002}\0"[i] == 'z' || "\U{0002}\0"[i] == 'Z');
}
method {:test} Test7() {
var r0 := ContainsZ("\U{0002}Z\U{0004}aaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}Z\U{0004}aaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa\U{0006}"| && ("\U{0002}Z\U{0004}aaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa\U{0006}"[i] == 'z' || "\U{0002}Z\U{0004}aaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa\U{0006}"[i] == 'Z');
}
method {:test} Test8() {
var r0 := ContainsZ("Za\U{0004}aaaa\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"Za\U{0004}aaaa\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa\U{0006}"| && ("Za\U{0004}aaaa\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa\U{0006}"[i] == 'z' || "Za\U{0004}aaaa\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaa\U{0006}"[i] == 'Z');
}

// REPEAT 3 - TIME: 76.3272832 s
