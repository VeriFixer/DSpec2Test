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

method {:test} Test16() {
var r0 := ToLowercase(",a-aaaaaaa2aaaaaaaaa>");
expect |r0| == |",a-aaaaaaa2aaaaaaaaa>"|;
expect forall i :: 0 <= i < |",a-aaaaaaa2aaaaaaaaa>"| ==> if IsUpperCase(",a-aaaaaaa2aaaaaaaaa>"[i]) then IsUpperLowerPair(",a-aaaaaaa2aaaaaaaaa>"[i], r0[i]) else r0[i] == ",a-aaaaaaa2aaaaaaaaa>"[i];
}
method {:test} Test17() {
var r0 := ToLowercase("\U{0010}aaaaaaaaa\U{0007}aaaaa>aaa\U{0005}aa<");
expect |r0| == |"\U{0010}aaaaaaaaa\U{0007}aaaaa>aaa\U{0005}aa<"|;
expect forall i :: 0 <= i < |"\U{0010}aaaaaaaaa\U{0007}aaaaa>aaa\U{0005}aa<"| ==> if IsUpperCase("\U{0010}aaaaaaaaa\U{0007}aaaaa>aaa\U{0005}aa<"[i]) then IsUpperLowerPair("\U{0010}aaaaaaaaa\U{0007}aaaaa>aaa\U{0005}aa<"[i], r0[i]) else r0[i] == "\U{0010}aaaaaaaaa\U{0007}aaaaa>aaa\U{0005}aa<"[i];
}
method {:test} Test18() {
var r0 := ToLowercase("<aaa");
expect |r0| == |"<aaa"|;
expect forall i :: 0 <= i < |"<aaa"| ==> if IsUpperCase("<aaa"[i]) then IsUpperLowerPair("<aaa"[i], r0[i]) else r0[i] == "<aaa"[i];
}
method {:test} Test19() {
var r0 := ToLowercase("a\U{0013}\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}aa\ta\U{0007}aaaa\U{0005}aaaaaaaaaaaaaaa\U{000B}");
expect |r0| == |"a\U{0013}\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}aa\ta\U{0007}aaaa\U{0005}aaaaaaaaaaaaaaa\U{000B}"|;
expect forall i :: 0 <= i < |"a\U{0013}\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}aa\ta\U{0007}aaaa\U{0005}aaaaaaaaaaaaaaa\U{000B}"| ==> if IsUpperCase("a\U{0013}\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}aa\ta\U{0007}aaaa\U{0005}aaaaaaaaaaaaaaa\U{000B}"[i]) then IsUpperLowerPair("a\U{0013}\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}aa\ta\U{0007}aaaa\U{0005}aaaaaaaaaaaaaaa\U{000B}"[i], r0[i]) else r0[i] == "a\U{0013}\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}aa\ta\U{0007}aaaa\U{0005}aaaaaaaaaaaaaaa\U{000B}"[i];
}

// REPEAT 5 - TIME: 14.3367011 s
