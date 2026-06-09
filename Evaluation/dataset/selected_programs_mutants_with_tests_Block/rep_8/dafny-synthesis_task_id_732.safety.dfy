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

method {:test} Test28() {
var r0 := ReplaceWithColon("aaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa\U{0001}\U{0002}");
expect |r0| == |"aaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa\U{0001}\U{0002}"|;
expect forall i :: 0 <= i < |"aaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa\U{0001}\U{0002}"| ==> (IsSpaceCommaDot("aaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa\U{0001}\U{0002}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa\U{0001}\U{0002}"[i]) ==> r0[i] == "aaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aaa\U{0001}\U{0002}"[i]);
}
method {:test} Test29() {
var r0 := ReplaceWithColon("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test31() {
var r0 := ReplaceWithColon("aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "aa\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 8 - TIME: 20.6891537 s
