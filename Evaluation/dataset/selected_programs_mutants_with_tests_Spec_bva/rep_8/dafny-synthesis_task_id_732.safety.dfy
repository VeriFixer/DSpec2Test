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

method {:test} Test16() {
var r0 := ReplaceWithColon("  aa   a");
expect |r0| == |"  aa   a"|;
expect forall i :: 0 <= i < |"  aa   a"| ==> (IsSpaceCommaDot("  aa   a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("  aa   a"[i]) ==> r0[i] == "  aa   a"[i]);
}

// REPEAT 8 - TIME: 12.2119379 s
