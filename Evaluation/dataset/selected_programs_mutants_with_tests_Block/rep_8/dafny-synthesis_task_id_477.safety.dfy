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

method {:test} Test28() {
var r0 := ToLowercase("aaaaaaaaaaaaaaaaaaaa\U{000F}aaaaaaaaaaaaaaaaaaaaa\U{0010}aa-a");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaa\U{000F}aaaaaaaaaaaaaaaaaaaaa\U{0010}aa-a"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaa\U{000F}aaaaaaaaaaaaaaaaaaaaa\U{0010}aa-a"| ==> if IsUpperCase("aaaaaaaaaaaaaaaaaaaa\U{000F}aaaaaaaaaaaaaaaaaaaaa\U{0010}aa-a"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaa\U{000F}aaaaaaaaaaaaaaaaaaaaa\U{0010}aa-a"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaa\U{000F}aaaaaaaaaaaaaaaaaaaaa\U{0010}aa-a"[i];
}
method {:test} Test29() {
var r0 := ToLowercase("-a-aaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"-a-aaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"-a-aaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("-a-aaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("-a-aaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "-a-aaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test30() {
var r0 := ToLowercase("aaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("aaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test31() {
var r0 := ToLowercase("a aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa");
expect |r0| == |"a aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa"|;
expect forall i :: 0 <= i < |"a aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa"| ==> if IsUpperCase("a aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa"[i]) then IsUpperLowerPair("a aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa"[i], r0[i]) else r0[i] == "a aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa"[i];
}

// REPEAT 8 - TIME: 22.1852951 s
