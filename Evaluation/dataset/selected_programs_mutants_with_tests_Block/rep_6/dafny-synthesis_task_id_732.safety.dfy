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

method {:test} Test20() {
var r0 := ReplaceWithColon(" aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa   aa\0a  ");
expect |r0| == |" aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa   aa\0a  "|;
expect forall i :: 0 <= i < |" aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa   aa\0a  "| ==> (IsSpaceCommaDot(" aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa   aa\0a  "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa   aa\0a  "[i]) ==> r0[i] == " aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa   aa\0a  "[i]);
}
method {:test} Test21() {
var r0 := ReplaceWithColon(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == " aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test23() {
var r0 := ReplaceWithColon("\0aa\U{0002}a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}a");
expect |r0| == |"\0aa\U{0002}a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}a"|;
expect forall i :: 0 <= i < |"\0aa\U{0002}a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}a"| ==> (IsSpaceCommaDot("\0aa\U{0002}a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0aa\U{0002}a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}a"[i]) ==> r0[i] == "\0aa\U{0002}a aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}a"[i]);
}

// REPEAT 6 - TIME: 17.8486768 s
