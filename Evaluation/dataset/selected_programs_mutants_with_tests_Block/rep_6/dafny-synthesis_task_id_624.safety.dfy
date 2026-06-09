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

method {:test} Test20() {
var r0 := ToUppercase("T");
expect |r0| == |"T"|;
expect forall i :: 0 <= i < |"T"| ==> if IsLowerCase("T"[i]) then IsLowerUpperPair("T"[i], r0[i]) else r0[i] == "T"[i];
}
method {:test} Test21() {
var r0 := ToUppercase("Qa<aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"Qa<aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"Qa<aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("Qa<aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("Qa<aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "Qa<aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test22() {
var r0 := ToUppercase(">a\U{0007}aa\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |">a\U{0007}aa\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |">a\U{0007}aa\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase(">a\U{0007}aa\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair(">a\U{0007}aa\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == ">a\U{0007}aa\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test23() {
var r0 := ToUppercase("\U{001C}_a\r\U{001B}");
expect |r0| == |"\U{001C}_a\r\U{001B}"|;
expect forall i :: 0 <= i < |"\U{001C}_a\r\U{001B}"| ==> if IsLowerCase("\U{001C}_a\r\U{001B}"[i]) then IsLowerUpperPair("\U{001C}_a\r\U{001B}"[i], r0[i]) else r0[i] == "\U{001C}_a\r\U{001B}"[i];
}

// REPEAT 6 - TIME: 15.5255208 s
