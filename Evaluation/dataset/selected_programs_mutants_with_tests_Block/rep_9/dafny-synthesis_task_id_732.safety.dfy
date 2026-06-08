predicate IsSpaceCommaDot(c: char)
{
    c == ' ' || c == ',' || c == '.'
}

method {:testEntry} ReplaceWithColon(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (IsSpaceCommaDot(s[i]) ==> v[i] == ':') && (!IsSpaceCommaDot(s[i]) ==> v[i] == s[i])
{
    var s' : string := [];
    for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i ==> (IsSpaceCommaDot(s[k]) ==> s'[k] == ':') && (!IsSpaceCommaDot(s[k]) ==> s'[k] == s[k])
    {
        if IsSpaceCommaDot(s[i])
        {
            s' := s' + [':'];
        }
        else 
        {
            s' := s' + [s[i]];
        }
    }
    return s';
}

method {:test} Test32() {
var r0 := ReplaceWithColon(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == " aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test33() {
var r0 := ReplaceWithColon("aaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "aaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test34() {
var r0 := ReplaceWithColon("a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test35() {
var r0 := ReplaceWithColon("a\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a");
expect |r0| == |"a\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a"|;
expect forall i :: 0 <= i < |"a\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a"| ==> (IsSpaceCommaDot("a\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a"[i]) ==> r0[i] == "a\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a"[i]);
}

// REPEAT 9 - TIME: 27.2193946 s
