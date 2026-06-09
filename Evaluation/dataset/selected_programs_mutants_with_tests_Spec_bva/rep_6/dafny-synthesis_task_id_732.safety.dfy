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

method {:test} Test14() {
var r0 := ReplaceWithColon(" aaaa aaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaa ");
expect |r0| == |" aaaa aaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaa "|;
expect forall i :: 0 <= i < |" aaaa aaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaa "| ==> (IsSpaceCommaDot(" aaaa aaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaa "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaa aaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaa "[i]) ==> r0[i] == " aaaa aaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaa "[i]);
}

// REPEAT 6 - TIME: 9.779965 s
