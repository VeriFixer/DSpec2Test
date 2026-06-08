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

method {:test} Test12() {
var r0 := ReplaceWithColon("aaa aaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaaaa ");
expect |r0| == |"aaa aaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaaaa "|;
expect forall i :: 0 <= i < |"aaa aaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaaaa "| ==> (IsSpaceCommaDot("aaa aaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaaaa "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaa aaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaaaa "[i]) ==> r0[i] == "aaa aaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaaaa "[i]);
}

// REPEAT 4 - TIME: 9.3193361 s
