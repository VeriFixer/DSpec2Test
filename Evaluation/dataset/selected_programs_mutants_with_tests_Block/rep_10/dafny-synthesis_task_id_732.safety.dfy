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

method {:test} Test36() {
var r0 := ReplaceWithColon("aaaa");
expect |r0| == |"aaaa"|;
expect forall i :: 0 <= i < |"aaaa"| ==> (IsSpaceCommaDot("aaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaa"[i]) ==> r0[i] == "aaaa"[i]);
}
method {:test} Test37() {
var r0 := ReplaceWithColon(":a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |":a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |":a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot(":a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(":a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ":a:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test38() {
var r0 := ReplaceWithColon("::");
expect |r0| == |"::"|;
expect forall i :: 0 <= i < |"::"| ==> (IsSpaceCommaDot("::"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("::"[i]) ==> r0[i] == "::"[i]);
}
method {:test} Test39() {
var r0 := ReplaceWithColon("aaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("aaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "aaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 10 - TIME: 30.9125357 s
