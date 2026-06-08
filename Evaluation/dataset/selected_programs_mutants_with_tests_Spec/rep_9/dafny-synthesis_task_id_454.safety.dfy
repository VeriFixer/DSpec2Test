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

method {:test} Test24() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaza\U{0003}\U{0001}\U{0005}");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaza\U{0003}\U{0001}\U{0005}"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaza\U{0003}\U{0001}\U{0005}"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaza\U{0003}\U{0001}\U{0005}"[i] == 'Z');
}
method {:test} Test25() {
var r0 := ContainsZ("\U{0001}aZ\U{0005}\U{0003}a");
expect r0 <==> exists i :: 0 <= i < |"\U{0001}aZ\U{0005}\U{0003}a"| && ("\U{0001}aZ\U{0005}\U{0003}a"[i] == 'z' || "\U{0001}aZ\U{0005}\U{0003}a"[i] == 'Z');
}
method {:test} Test26() {
var r0 := ContainsZ("\U{0002}aaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}"| && ("\U{0002}aaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}"[i] == 'z' || "\U{0002}aaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaa\U{0006}a\U{0004}"[i] == 'Z');
}

// REPEAT 9 - TIME: 20.0319042 s
