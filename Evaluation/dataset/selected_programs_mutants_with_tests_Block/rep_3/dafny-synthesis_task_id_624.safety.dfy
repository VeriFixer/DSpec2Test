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

method {:test} Test8() {
var r0 := ToUppercase("Ta");
expect |r0| == |"Ta"|;
expect forall i :: 0 <= i < |"Ta"| ==> if IsLowerCase("Ta"[i]) then IsLowerUpperPair("Ta"[i], r0[i]) else r0[i] == "Ta"[i];
}
method {:test} Test9() {
var r0 := ToUppercase("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> if IsLowerCase(""[i]) then IsLowerUpperPair(""[i], r0[i]) else r0[i] == ""[i];
}
method {:test} Test10() {
var r0 := ToUppercase("\U{0018}");
expect |r0| == |"\U{0018}"|;
expect forall i :: 0 <= i < |"\U{0018}"| ==> if IsLowerCase("\U{0018}"[i]) then IsLowerUpperPair("\U{0018}"[i], r0[i]) else r0[i] == "\U{0018}"[i];
}
method {:test} Test11() {
var r0 := ToUppercase("\U{000C}:");
expect |r0| == |"\U{000C}:"|;
expect forall i :: 0 <= i < |"\U{000C}:"| ==> if IsLowerCase("\U{000C}:"[i]) then IsLowerUpperPair("\U{000C}:"[i], r0[i]) else r0[i] == "\U{000C}:"[i];
}

// REPEAT 3 - TIME: 9.8785922 s
