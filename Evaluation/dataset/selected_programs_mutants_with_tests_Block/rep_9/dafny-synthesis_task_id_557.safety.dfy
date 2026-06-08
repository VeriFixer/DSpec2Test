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

method {:test} Test48() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test51() {
var r0 := ToggleCase("Ya");
expect |r0| == |"Ya"|;
expect forall i :: 0 <= i < |"Ya"| ==> if IsLowerCase("Ya"[i]) then IsLowerUpperPair("Ya"[i], r0[i]) else if IsUpperCase("Ya"[i]) then IsUpperLowerPair("Ya"[i], r0[i]) else r0[i] == "Ya"[i];
}
method {:test} Test53() {
var r0 := ToggleCase("aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaDaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}

// REPEAT 9 - TIME: 34.4552137 s
