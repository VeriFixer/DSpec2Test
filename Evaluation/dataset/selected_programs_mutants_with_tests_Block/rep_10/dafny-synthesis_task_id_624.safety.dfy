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

method {:test} Test36() {
var r0 := ToUppercase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa&");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa&"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa&"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa&"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa&"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa&"[i];
}
method {:test} Test37() {
var r0 := ToUppercase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test39() {
var r0 := ToUppercase("aaaaaaaaaaaaaaaa$aaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}a\U{0005}");
expect |r0| == |"aaaaaaaaaaaaaaaa$aaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}a\U{0005}"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaa$aaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}a\U{0005}"| ==> if IsLowerCase("aaaaaaaaaaaaaaaa$aaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}a\U{0005}"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaa$aaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}a\U{0005}"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaa$aaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}a\U{0005}"[i];
}

// REPEAT 10 - TIME: 26.8914509 s
