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

method {:test} Test0() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz"[i] == 'Z');
}
method {:test} Test1() {
var r0 := ContainsZ("z");
expect r0 <==> exists i :: 0 <= i < |"z"| && ("z"[i] == 'z' || "z"[i] == 'Z');
}
method {:test} Test2() {
var r0 := ContainsZ("za");
expect r0 <==> exists i :: 0 <= i < |"za"| && ("za"[i] == 'z' || "za"[i] == 'Z');
}
method {:test} Test7() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"[i] == 'Z');
}
method {:test} Test8() {
var r0 := ContainsZ("Z");
expect r0 <==> exists i :: 0 <= i < |"Z"| && ("Z"[i] == 'z' || "Z"[i] == 'Z');
}
method {:test} Test9() {
var r0 := ContainsZ("Za");
expect r0 <==> exists i :: 0 <= i < |"Za"| && ("Za"[i] == 'z' || "Za"[i] == 'Z');
}
method {:test} Test14() {
var r0 := ContainsZ("");
expect r0 <==> exists i :: 0 <= i < |""| && (""[i] == 'z' || ""[i] == 'Z');
}
method {:test} Test16() {
var r0 := ContainsZ("a");
expect r0 <==> exists i :: 0 <= i < |"a"| && ("a"[i] == 'z' || "a"[i] == 'Z');
}
method {:test} Test17() {
var r0 := ContainsZ("aa");
expect r0 <==> exists i :: 0 <= i < |"aa"| && ("aa"[i] == 'z' || "aa"[i] == 'Z');
}

// REPEAT 1 - TIME: 11.4392337 s