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
var r0 := ReplaceWithColon(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a  a a ");
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a  a a "|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a  a a "| ==> (IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a  a a "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a  a a "[i]) ==> r0[i] == " aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa a  a a "[i]);
}
method {:test} Test17() {
var r0 := ReplaceWithColon("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> (IsSpaceCommaDot("\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0"[i]) ==> r0[i] == "\0"[i]);
}
method {:test} Test18() {
var r0 := ReplaceWithColon("\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "\0a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 5 - TIME: 13.3163485 s
