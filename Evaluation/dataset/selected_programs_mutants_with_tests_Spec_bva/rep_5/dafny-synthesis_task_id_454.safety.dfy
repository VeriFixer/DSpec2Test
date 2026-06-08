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

method {:test} Test31() {
var r0 := ContainsZ("\U{000B}aaaaaaaaaaa\U{0001}a\U{0005}\U{0007}aaa\U{000F}aaa\U{0003}\taaaaaaaaaaaaaz\U{0011}\U{0015}aaaa\U{0013}\raaa");
expect r0 <==> exists i :: 0 <= i < |"\U{000B}aaaaaaaaaaa\U{0001}a\U{0005}\U{0007}aaa\U{000F}aaa\U{0003}\taaaaaaaaaaaaaz\U{0011}\U{0015}aaaa\U{0013}\raaa"| && ("\U{000B}aaaaaaaaaaa\U{0001}a\U{0005}\U{0007}aaa\U{000F}aaa\U{0003}\taaaaaaaaaaaaaz\U{0011}\U{0015}aaaa\U{0013}\raaa"[i] == 'z' || "\U{000B}aaaaaaaaaaa\U{0001}a\U{0005}\U{0007}aaa\U{000F}aaa\U{0003}\taaaaaaaaaaaaaz\U{0011}\U{0015}aaaa\U{0013}\raaa"[i] == 'Z');
}
method {:test} Test32() {
var r0 := ContainsZ("\U{0003}\U{0001}aZaaaa");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}\U{0001}aZaaaa"| && ("\U{0003}\U{0001}aZaaaa"[i] == 'z' || "\U{0003}\U{0001}aZaaaa"[i] == 'Z');
}
method {:test} Test33() {
var r0 := ContainsZ("\U{000C}\0\U{000E}aaaaaaaa\U{0002}aaaa\U{0008}aa\U{0004}aaa\n\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\U{000C}\0\U{000E}aaaaaaaa\U{0002}aaaa\U{0008}aa\U{0004}aaa\n\U{0006}"| && ("\U{000C}\0\U{000E}aaaaaaaa\U{0002}aaaa\U{0008}aa\U{0004}aaa\n\U{0006}"[i] == 'z' || "\U{000C}\0\U{000E}aaaaaaaa\U{0002}aaaa\U{0008}aa\U{0004}aaa\n\U{0006}"[i] == 'Z');
}

// REPEAT 5 - TIME: 18.936701 s
