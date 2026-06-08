predicate IsLowerCase(c : char)
{
    97 <= c as int <= 122
}

predicate IsLowerUpperPair(c : char, C : char)
{
    (c as int) == (C as int) + 32
}

function ShiftMinus32(c : char) :  char
{
    ((c as int - 32) % 128) as char
}

method {:testEntry} ToUppercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i]
{
    var s' : string := [];
    for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i &&  IsLowerCase(s[k]) ==> IsLowerUpperPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i && !IsLowerCase(s[k]) ==> s[k] == s'[k]
    {
        if IsLowerCase(s[i])
        {
            s' := s' + [ShiftMinus32(s[i])];
        }
        else 
        {
            s' := s' + [s[i]];
        }
    }
    return s';
}

method {:test} Test16() {
var r0 := ToUppercase("\U{001C}\U{000C}8a");
expect |r0| == |"\U{001C}\U{000C}8a"|;
expect forall i :: 0 <= i < |"\U{001C}\U{000C}8a"| ==> if IsLowerCase("\U{001C}\U{000C}8a"[i]) then IsLowerUpperPair("\U{001C}\U{000C}8a"[i], r0[i]) else r0[i] == "\U{001C}\U{000C}8a"[i];
}

// REPEAT 8 - TIME: 13.7974755 s
