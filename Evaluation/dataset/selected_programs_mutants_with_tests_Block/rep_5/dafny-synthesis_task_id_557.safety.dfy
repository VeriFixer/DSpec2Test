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

method {:test} Test24() {
var r0 := ToggleCase("gaabaaaaaacqa");
expect |r0| == |"gaabaaaaaacqa"|;
expect forall i :: 0 <= i < |"gaabaaaaaacqa"| ==> if IsLowerCase("gaabaaaaaacqa"[i]) then IsLowerUpperPair("gaabaaaaaacqa"[i], r0[i]) else if IsUpperCase("gaabaaaaaacqa"[i]) then IsUpperLowerPair("gaabaaaaaacqa"[i], r0[i]) else r0[i] == "gaabaaaaaacqa"[i];
}
method {:test} Test25() {
var r0 := ToggleCase("\U{D0FB}a");
expect |r0| == |"\U{D0FB}a"|;
expect forall i :: 0 <= i < |"\U{D0FB}a"| ==> if IsLowerCase("\U{D0FB}a"[i]) then IsLowerUpperPair("\U{D0FB}a"[i], r0[i]) else if IsUpperCase("\U{D0FB}a"[i]) then IsUpperLowerPair("\U{D0FB}a"[i], r0[i]) else r0[i] == "\U{D0FB}a"[i];
}
method {:test} Test26() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test27() {
var r0 := ToggleCase("Caaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"Caaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"Caaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("Caaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("Caaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("Caaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("Caaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "Caaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test28() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test29() {
var r0 := ToggleCase("Daa\U{0001}gg");
expect |r0| == |"Daa\U{0001}gg"|;
expect forall i :: 0 <= i < |"Daa\U{0001}gg"| ==> if IsLowerCase("Daa\U{0001}gg"[i]) then IsLowerUpperPair("Daa\U{0001}gg"[i], r0[i]) else if IsUpperCase("Daa\U{0001}gg"[i]) then IsUpperLowerPair("Daa\U{0001}gg"[i], r0[i]) else r0[i] == "Daa\U{0001}gg"[i];
}

// REPEAT 5 - TIME: 18.48542 s
