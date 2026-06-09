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

method {:test} Test18() {
var r0 := ToggleCase("gacayaaaajqa");
expect |r0| == |"gacayaaaajqa"|;
expect forall i :: 0 <= i < |"gacayaaaajqa"| ==> if IsLowerCase("gacayaaaajqa"[i]) then IsLowerUpperPair("gacayaaaajqa"[i], r0[i]) else if IsUpperCase("gacayaaaajqa"[i]) then IsUpperLowerPair("gacayaaaajqa"[i], r0[i]) else r0[i] == "gacayaaaajqa"[i];
}
method {:test} Test19() {
var r0 := ToggleCase("Kaa");
expect |r0| == |"Kaa"|;
expect forall i :: 0 <= i < |"Kaa"| ==> if IsLowerCase("Kaa"[i]) then IsLowerUpperPair("Kaa"[i], r0[i]) else if IsUpperCase("Kaa"[i]) then IsUpperLowerPair("Kaa"[i], r0[i]) else r0[i] == "Kaa"[i];
}
method {:test} Test20() {
var r0 := ToggleCase("7a");
expect |r0| == |"7a"|;
expect forall i :: 0 <= i < |"7a"| ==> if IsLowerCase("7a"[i]) then IsLowerUpperPair("7a"[i], r0[i]) else if IsUpperCase("7a"[i]) then IsUpperLowerPair("7a"[i], r0[i]) else r0[i] == "7a"[i];
}
method {:test} Test21() {
var r0 := ToggleCase(".");
expect |r0| == |"."|;
expect forall i :: 0 <= i < |"."| ==> if IsLowerCase("."[i]) then IsLowerUpperPair("."[i], r0[i]) else if IsUpperCase("."[i]) then IsUpperLowerPair("."[i], r0[i]) else r0[i] == "."[i];
}
method {:test} Test22() {
var r0 := ToggleCase("\U{0005}aa");
expect |r0| == |"\U{0005}aa"|;
expect forall i :: 0 <= i < |"\U{0005}aa"| ==> if IsLowerCase("\U{0005}aa"[i]) then IsLowerUpperPair("\U{0005}aa"[i], r0[i]) else if IsUpperCase("\U{0005}aa"[i]) then IsUpperLowerPair("\U{0005}aa"[i], r0[i]) else r0[i] == "\U{0005}aa"[i];
}
method {:test} Test23() {
var r0 := ToggleCase("bT\U{0004}\U{0006}\0");
expect |r0| == |"bT\U{0004}\U{0006}\0"|;
expect forall i :: 0 <= i < |"bT\U{0004}\U{0006}\0"| ==> if IsLowerCase("bT\U{0004}\U{0006}\0"[i]) then IsLowerUpperPair("bT\U{0004}\U{0006}\0"[i], r0[i]) else if IsUpperCase("bT\U{0004}\U{0006}\0"[i]) then IsUpperLowerPair("bT\U{0004}\U{0006}\0"[i], r0[i]) else r0[i] == "bT\U{0004}\U{0006}\0"[i];
}

// REPEAT 4 - TIME: 14.3644382 s
