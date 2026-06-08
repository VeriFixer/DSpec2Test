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

method {:test} Test30() {
var r0 := ToggleCase("gaaaaaa");
expect |r0| == |"gaaaaaa"|;
expect forall i :: 0 <= i < |"gaaaaaa"| ==> if IsLowerCase("gaaaaaa"[i]) then IsLowerUpperPair("gaaaaaa"[i], r0[i]) else if IsUpperCase("gaaaaaa"[i]) then IsUpperLowerPair("gaaaaaa"[i], r0[i]) else r0[i] == "gaaaaaa"[i];
}
method {:test} Test31() {
var r0 := ToggleCase("haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "haaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test32() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test34() {
var r0 := ToggleCase("paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "paaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test35() {
var r0 := ToggleCase("aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaDaaaaaaaaagaaaaaaaaaaaaaaaaaaaaaaa"[i];
}

// REPEAT 6 - TIME: 22.053277 s
