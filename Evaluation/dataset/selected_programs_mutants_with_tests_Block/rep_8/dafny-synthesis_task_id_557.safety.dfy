predicate IsLowerCase(c : char)
{
    97 <= c as int <= 122
}

predicate IsUpperCase(c : char)
{
    65 <= c as int <= 90
}

predicate IsLowerUpperPair(c : char, C : char)
{
    (c as int) == (C as int) + 32
}

predicate IsUpperLowerPair(C : char, c : char)
{
    (C as int) == (c as int) - 32
}

function ShiftMinus32(c : char) :  char
{
    ((c as int - 32) % 128) as char
}

function Shift32(c : char) :  char
{
    ((c as int + 32) % 128) as char
}

method {:testEntry} ToggleCase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{
    var s' : string := [];
    for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i &&  IsLowerCase(s[k]) ==> IsLowerUpperPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i &&  IsUpperCase(s[k]) ==> IsUpperLowerPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i && !IsLowerCase(s[k]) && !IsUpperCase(s[k]) ==> s[k] == s'[k]
    {
        if IsLowerCase(s[i])
        {
            s' := s' + [ShiftMinus32(s[i])];
        }
        else if IsUpperCase(s[i])
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

method {:test} Test42() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaagaa"[i];
}
method {:test} Test43() {
var r0 := ToggleCase("\U{000F}a");
expect |r0| == |"\U{000F}a"|;
expect forall i :: 0 <= i < |"\U{000F}a"| ==> if IsLowerCase("\U{000F}a"[i]) then IsLowerUpperPair("\U{000F}a"[i], r0[i]) else if IsUpperCase("\U{000F}a"[i]) then IsUpperLowerPair("\U{000F}a"[i], r0[i]) else r0[i] == "\U{000F}a"[i];
}
method {:test} Test44() {
var r0 := ToggleCase("\U{0007}a");
expect |r0| == |"\U{0007}a"|;
expect forall i :: 0 <= i < |"\U{0007}a"| ==> if IsLowerCase("\U{0007}a"[i]) then IsLowerUpperPair("\U{0007}a"[i], r0[i]) else if IsUpperCase("\U{0007}a"[i]) then IsUpperLowerPair("\U{0007}a"[i], r0[i]) else r0[i] == "\U{0007}a"[i];
}
method {:test} Test45() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test47() {
var r0 := ToggleCase("aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aTaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}

// REPEAT 8 - TIME: 26.7138263 s
