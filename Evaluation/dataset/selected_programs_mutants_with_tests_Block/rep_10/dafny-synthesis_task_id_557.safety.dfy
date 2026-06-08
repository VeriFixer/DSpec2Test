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

method {:test} Test54() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test55() {
var r0 := ToggleCase("\U{0010}a");
expect |r0| == |"\U{0010}a"|;
expect forall i :: 0 <= i < |"\U{0010}a"| ==> if IsLowerCase("\U{0010}a"[i]) then IsLowerUpperPair("\U{0010}a"[i], r0[i]) else if IsUpperCase("\U{0010}a"[i]) then IsUpperLowerPair("\U{0010}a"[i], r0[i]) else r0[i] == "\U{0010}a"[i];
}
method {:test} Test56() {
var r0 := ToggleCase("\U{0019}a");
expect |r0| == |"\U{0019}a"|;
expect forall i :: 0 <= i < |"\U{0019}a"| ==> if IsLowerCase("\U{0019}a"[i]) then IsLowerUpperPair("\U{0019}a"[i], r0[i]) else if IsUpperCase("\U{0019}a"[i]) then IsUpperLowerPair("\U{0019}a"[i], r0[i]) else r0[i] == "\U{0019}a"[i];
}
method {:test} Test58() {
var r0 := ToggleCase("2a");
expect |r0| == |"2a"|;
expect forall i :: 0 <= i < |"2a"| ==> if IsLowerCase("2a"[i]) then IsLowerUpperPair("2a"[i], r0[i]) else if IsUpperCase("2a"[i]) then IsUpperLowerPair("2a"[i], r0[i]) else r0[i] == "2a"[i];
}
method {:test} Test59() {
var r0 := ToggleCase("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}

// REPEAT 10 - TIME: 39.017784 s
