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

method {:test} Test18() {
var r0 := ReplaceWithColon("\U{0005}aaaaa\U{0002}a\U{0003}\U{0004}aaaaaaa\0aaa\U{0001}aaaaa");
expect |r0| == |"\U{0005}aaaaa\U{0002}a\U{0003}\U{0004}aaaaaaa\0aaa\U{0001}aaaaa"|;
expect forall i :: 0 <= i < |"\U{0005}aaaaa\U{0002}a\U{0003}\U{0004}aaaaaaa\0aaa\U{0001}aaaaa"| ==> (IsSpaceCommaDot("\U{0005}aaaaa\U{0002}a\U{0003}\U{0004}aaaaaaa\0aaa\U{0001}aaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\U{0005}aaaaa\U{0002}a\U{0003}\U{0004}aaaaaaa\0aaa\U{0001}aaaaa"[i]) ==> r0[i] == "\U{0005}aaaaa\U{0002}a\U{0003}\U{0004}aaaaaaa\0aaa\U{0001}aaaaa"[i]);
}

// REPEAT 10 - TIME: 12.2204044 s
