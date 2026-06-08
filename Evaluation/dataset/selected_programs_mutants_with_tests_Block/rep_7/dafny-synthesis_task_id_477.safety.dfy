predicate IsUpperCase(c : char)
{
    65 <= c as int <= 90
}

predicate IsUpperLowerPair(C : char, c : char)
{
    (C as int) == (c as int) - 32
}

function Shift32(c : char) :  char
{
    ((c as int + 32) % 128) as char
}

method {:testEntry} ToLowercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{
    var s' : string := [];
    for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i &&  IsUpperCase(s[k]) ==> IsUpperLowerPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i && !IsUpperCase(s[k]) ==> s[k] == s'[k]
    {
        if IsUpperCase(s[i])
        {
            s' := s' + [Shift32(s[i])];
        }
        else 
        {
            s' := s' + [s[i]];
        }
    }
    return s';
}

method {:test} Test24() {
var r0 := ToLowercase(" aaa\U{000F}");
expect |r0| == |" aaa\U{000F}"|;
expect forall i :: 0 <= i < |" aaa\U{000F}"| ==> if IsUpperCase(" aaa\U{000F}"[i]) then IsUpperLowerPair(" aaa\U{000F}"[i], r0[i]) else r0[i] == " aaa\U{000F}"[i];
}
method {:test} Test25() {
var r0 := ToLowercase("&aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"&aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"&aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("&aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("&aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "&aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test26() {
var r0 := ToLowercase(",a\U{0007}aaa");
expect |r0| == |",a\U{0007}aaa"|;
expect forall i :: 0 <= i < |",a\U{0007}aaa"| ==> if IsUpperCase(",a\U{0007}aaa"[i]) then IsUpperLowerPair(",a\U{0007}aaa"[i], r0[i]) else r0[i] == ",a\U{0007}aaa"[i];
}
method {:test} Test27() {
var r0 := ToLowercase("-a\U{0013}aaaaaaaaaaaaaaaaaa\U{0001}aaa\U{0008}aaaaaaaa\U{0004}aaaa\U{0006}aaa\naaaa");
expect |r0| == |"-a\U{0013}aaaaaaaaaaaaaaaaaa\U{0001}aaa\U{0008}aaaaaaaa\U{0004}aaaa\U{0006}aaa\naaaa"|;
expect forall i :: 0 <= i < |"-a\U{0013}aaaaaaaaaaaaaaaaaa\U{0001}aaa\U{0008}aaaaaaaa\U{0004}aaaa\U{0006}aaa\naaaa"| ==> if IsUpperCase("-a\U{0013}aaaaaaaaaaaaaaaaaa\U{0001}aaa\U{0008}aaaaaaaa\U{0004}aaaa\U{0006}aaa\naaaa"[i]) then IsUpperLowerPair("-a\U{0013}aaaaaaaaaaaaaaaaaa\U{0001}aaa\U{0008}aaaaaaaa\U{0004}aaaa\U{0006}aaa\naaaa"[i], r0[i]) else r0[i] == "-a\U{0013}aaaaaaaaaaaaaaaaaa\U{0001}aaa\U{0008}aaaaaaaa\U{0004}aaaa\U{0006}aaa\naaaa"[i];
}

// REPEAT 7 - TIME: 19.2424195 s
