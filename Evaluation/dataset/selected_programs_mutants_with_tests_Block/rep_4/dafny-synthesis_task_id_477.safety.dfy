predicate IsUpperCase(c : char)
{
    65 <= c as int <= 90
}

predicate IsUpperLowerPair(C : char, c : char)
{
    (C as int) == (c as int) - 32
}

function Shift32(c : char) :  char
{
    ((c as int + 32) % 128) as char
}

method {:testEntry} ToLowercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{
    var s' : string := [];
    for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i &&  IsUpperCase(s[k]) ==> IsUpperLowerPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i && !IsUpperCase(s[k]) ==> s[k] == s'[k]
    {
        if IsUpperCase(s[i])
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
var r0 := ToLowercase("4@a");
expect |r0| == |"4@a"|;
expect forall i :: 0 <= i < |"4@a"| ==> if IsUpperCase("4@a"[i]) then IsUpperLowerPair("4@a"[i], r0[i]) else r0[i] == "4@a"[i];
}
method {:test} Test13() {
var r0 := ToLowercase("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> if IsUpperCase(""[i]) then IsUpperLowerPair(""[i], r0[i]) else r0[i] == ""[i];
}
method {:test} Test15() {
var r0 := ToLowercase(" 1aaaaaaaaaa\0aaaaaa\U{0001}");
expect |r0| == |" 1aaaaaaaaaa\0aaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |" 1aaaaaaaaaa\0aaaaaa\U{0001}"| ==> if IsUpperCase(" 1aaaaaaaaaa\0aaaaaa\U{0001}"[i]) then IsUpperLowerPair(" 1aaaaaaaaaa\0aaaaaa\U{0001}"[i], r0[i]) else r0[i] == " 1aaaaaaaaaa\0aaaaaa\U{0001}"[i];
}

// REPEAT 4 - TIME: 11.6282007 s
