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

method {:test} Test13() {
var r0 := ReplaceWithColon("aaaa ");
expect |r0| == |"aaaa "|;
expect forall i :: 0 <= i < |"aaaa "| ==> (IsSpaceCommaDot("aaaa "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaa "[i]) ==> r0[i] == "aaaa "[i]);
}

// REPEAT 5 - TIME: 8.9764454 s
