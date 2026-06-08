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
var r0 := ToUppercase("(aa\\");
expect |r0| == |"(aa\\"|;
expect forall i :: 0 <= i < |"(aa\\"| ==> if IsLowerCase("(aa\\"[i]) then IsLowerUpperPair("(aa\\"[i], r0[i]) else r0[i] == "(aa\\"[i];
}
method {:test} Test17() {
var r0 := ToUppercase("\U{0018}aW");
expect |r0| == |"\U{0018}aW"|;
expect forall i :: 0 <= i < |"\U{0018}aW"| ==> if IsLowerCase("\U{0018}aW"[i]) then IsLowerUpperPair("\U{0018}aW"[i], r0[i]) else r0[i] == "\U{0018}aW"[i];
}
method {:test} Test18() {
var r0 := ToUppercase("\U{0015}aaa");
expect |r0| == |"\U{0015}aaa"|;
expect forall i :: 0 <= i < |"\U{0015}aaa"| ==> if IsLowerCase("\U{0015}aaa"[i]) then IsLowerUpperPair("\U{0015}aaa"[i], r0[i]) else r0[i] == "\U{0015}aaa"[i];
}
method {:test} Test19() {
var r0 := ToUppercase("\U{0017}\U{0004}aaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0004}");
expect |r0| == |"\U{0017}\U{0004}aaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0004}"|;
expect forall i :: 0 <= i < |"\U{0017}\U{0004}aaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0004}"| ==> if IsLowerCase("\U{0017}\U{0004}aaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0004}"[i]) then IsLowerUpperPair("\U{0017}\U{0004}aaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0004}"[i], r0[i]) else r0[i] == "\U{0017}\U{0004}aaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0004}"[i];
}

// REPEAT 5 - TIME: 14.3787393 s
