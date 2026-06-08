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

method {:test} Test20() {
var r0 := ToLowercase("%aaaaaaaaaaaa=a\U{0014}");
expect |r0| == |"%aaaaaaaaaaaa=a\U{0014}"|;
expect forall i :: 0 <= i < |"%aaaaaaaaaaaa=a\U{0014}"| ==> if IsUpperCase("%aaaaaaaaaaaa=a\U{0014}"[i]) then IsUpperLowerPair("%aaaaaaaaaaaa=a\U{0014}"[i], r0[i]) else r0[i] == "%aaaaaaaaaaaa=a\U{0014}"[i];
}
method {:test} Test21() {
var r0 := ToLowercase("\U{001E}\U{001D}a");
expect |r0| == |"\U{001E}\U{001D}a"|;
expect forall i :: 0 <= i < |"\U{001E}\U{001D}a"| ==> if IsUpperCase("\U{001E}\U{001D}a"[i]) then IsUpperLowerPair("\U{001E}\U{001D}a"[i], r0[i]) else r0[i] == "\U{001E}\U{001D}a"[i];
}
method {:test} Test22() {
var r0 := ToLowercase("\U{0015}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{0015}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0015}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("\U{0015}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("\U{0015}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{0015}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test23() {
var r0 := ToLowercase("a\U{000F}aaa\0a");
expect |r0| == |"a\U{000F}aaa\0a"|;
expect forall i :: 0 <= i < |"a\U{000F}aaa\0a"| ==> if IsUpperCase("a\U{000F}aaa\0a"[i]) then IsUpperLowerPair("a\U{000F}aaa\0a"[i], r0[i]) else r0[i] == "a\U{000F}aaa\0a"[i];
}

// REPEAT 6 - TIME: 16.6700012 s
