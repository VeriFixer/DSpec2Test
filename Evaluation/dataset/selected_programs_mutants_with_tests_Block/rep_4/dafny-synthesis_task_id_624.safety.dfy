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

method {:test} Test12() {
var r0 := ToUppercase("$a");
expect |r0| == |"$a"|;
expect forall i :: 0 <= i < |"$a"| ==> if IsLowerCase("$a"[i]) then IsLowerUpperPair("$a"[i], r0[i]) else r0[i] == "$a"[i];
}
method {:test} Test13() {
var r0 := ToUppercase("a\U{0017}<");
expect |r0| == |"a\U{0017}<"|;
expect forall i :: 0 <= i < |"a\U{0017}<"| ==> if IsLowerCase("a\U{0017}<"[i]) then IsLowerUpperPair("a\U{0017}<"[i], r0[i]) else r0[i] == "a\U{0017}<"[i];
}
method {:test} Test14() {
var r0 := ToUppercase("\U{0007}\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{0007}\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0007}\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("\U{0007}\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("\U{0007}\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{0007}\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test15() {
var r0 := ToUppercase("(");
expect |r0| == |"("|;
expect forall i :: 0 <= i < |"("| ==> if IsLowerCase("("[i]) then IsLowerUpperPair("("[i], r0[i]) else r0[i] == "("[i];
}

// REPEAT 4 - TIME: 12.3000212 s
