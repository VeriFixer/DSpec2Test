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

method {:test} Test12() {
var r0 := ToggleCase("kaag");
expect |r0| == |"kaag"|;
expect forall i :: 0 <= i < |"kaag"| ==> if IsLowerCase("kaag"[i]) then IsLowerUpperPair("kaag"[i], r0[i]) else if IsUpperCase("kaag"[i]) then IsUpperLowerPair("kaag"[i], r0[i]) else r0[i] == "kaag"[i];
}
method {:test} Test13() {
var r0 := ToggleCase("[C\U{0015}a");
expect |r0| == |"[C\U{0015}a"|;
expect forall i :: 0 <= i < |"[C\U{0015}a"| ==> if IsLowerCase("[C\U{0015}a"[i]) then IsLowerUpperPair("[C\U{0015}a"[i], r0[i]) else if IsUpperCase("[C\U{0015}a"[i]) then IsUpperLowerPair("[C\U{0015}a"[i], r0[i]) else r0[i] == "[C\U{0015}a"[i];
}
method {:test} Test14() {
var r0 := ToggleCase("sa");
expect |r0| == |"sa"|;
expect forall i :: 0 <= i < |"sa"| ==> if IsLowerCase("sa"[i]) then IsLowerUpperPair("sa"[i], r0[i]) else if IsUpperCase("sa"[i]) then IsUpperLowerPair("sa"[i], r0[i]) else r0[i] == "sa"[i];
}
method {:test} Test15() {
var r0 := ToggleCase("-");
expect |r0| == |"-"|;
expect forall i :: 0 <= i < |"-"| ==> if IsLowerCase("-"[i]) then IsLowerUpperPair("-"[i], r0[i]) else if IsUpperCase("-"[i]) then IsUpperLowerPair("-"[i], r0[i]) else r0[i] == "-"[i];
}
method {:test} Test16() {
var r0 := ToggleCase("araa");
expect |r0| == |"araa"|;
expect forall i :: 0 <= i < |"araa"| ==> if IsLowerCase("araa"[i]) then IsLowerUpperPair("araa"[i], r0[i]) else if IsUpperCase("araa"[i]) then IsUpperLowerPair("araa"[i], r0[i]) else r0[i] == "araa"[i];
}
method {:test} Test17() {
var r0 := ToggleCase("g\U{0004}bg");
expect |r0| == |"g\U{0004}bg"|;
expect forall i :: 0 <= i < |"g\U{0004}bg"| ==> if IsLowerCase("g\U{0004}bg"[i]) then IsLowerUpperPair("g\U{0004}bg"[i], r0[i]) else if IsUpperCase("g\U{0004}bg"[i]) then IsUpperLowerPair("g\U{0004}bg"[i], r0[i]) else r0[i] == "g\U{0004}bg"[i];
}

// REPEAT 3 - TIME: 12.642103 s
