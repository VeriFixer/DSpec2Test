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

method {:test} Test8() {
var r0 := ToLowercase(" a\U{000F}");
expect |r0| == |" a\U{000F}"|;
expect forall i :: 0 <= i < |" a\U{000F}"| ==> if IsUpperCase(" a\U{000F}"[i]) then IsUpperLowerPair(" a\U{000F}"[i], r0[i]) else r0[i] == " a\U{000F}"[i];
}
method {:test} Test9() {
var r0 := ToLowercase("%aaaaaa\U{0003}aaaaaa>");
expect |r0| == |"%aaaaaa\U{0003}aaaaaa>"|;
expect forall i :: 0 <= i < |"%aaaaaa\U{0003}aaaaaa>"| ==> if IsUpperCase("%aaaaaa\U{0003}aaaaaa>"[i]) then IsUpperLowerPair("%aaaaaa\U{0003}aaaaaa>"[i], r0[i]) else r0[i] == "%aaaaaa\U{0003}aaaaaa>"[i];
}
method {:test} Test10() {
var r0 := ToLowercase("\n");
expect |r0| == |"\n"|;
expect forall i :: 0 <= i < |"\n"| ==> if IsUpperCase("\n"[i]) then IsUpperLowerPair("\n"[i], r0[i]) else r0[i] == "\n"[i];
}
method {:test} Test11() {
var r0 := ToLowercase(" a\U{0001}aaaaaaaaaaaaaaaaaaaaa\0");
expect |r0| == |" a\U{0001}aaaaaaaaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |" a\U{0001}aaaaaaaaaaaaaaaaaaaaa\0"| ==> if IsUpperCase(" a\U{0001}aaaaaaaaaaaaaaaaaaaaa\0"[i]) then IsUpperLowerPair(" a\U{0001}aaaaaaaaaaaaaaaaaaaaa\0"[i], r0[i]) else r0[i] == " a\U{0001}aaaaaaaaaaaaaaaaaaaaa\0"[i];
}

// REPEAT 3 - TIME: 9.2402387 s
