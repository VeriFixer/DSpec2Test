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
var r0 := ReplaceWithColon("aaaaaaaaaaaaa aaaaaaaaaaaaaaaaaaaaaaaaaa a ");
expect |r0| == |"aaaaaaaaaaaaa aaaaaaaaaaaaaaaaaaaaaaaaaa a "|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaa aaaaaaaaaaaaaaaaaaaaaaaaaa a "| ==> (IsSpaceCommaDot("aaaaaaaaaaaaa aaaaaaaaaaaaaaaaaaaaaaaaaa a "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaaaaaaaaaaa aaaaaaaaaaaaaaaaaaaaaaaaaa a "[i]) ==> r0[i] == "aaaaaaaaaaaaa aaaaaaaaaaaaaaaaaaaaaaaaaa a "[i]);
}
method {:test} Test13() {
var r0 := ReplaceWithColon("\0\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\0\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\0\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("\0\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "\0\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test14() {
var r0 := ReplaceWithColon(":\0");
expect |r0| == |":\0"|;
expect forall i :: 0 <= i < |":\0"| ==> (IsSpaceCommaDot(":\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(":\0"[i]) ==> r0[i] == ":\0"[i]);
}
method {:test} Test15() {
var r0 := ReplaceWithColon("a\0a\U{0006}a\U{0001}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaa\U{0002}\U{0008}a\naa\U{000C}a");
expect |r0| == |"a\0a\U{0006}a\U{0001}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaa\U{0002}\U{0008}a\naa\U{000C}a"|;
expect forall i :: 0 <= i < |"a\0a\U{0006}a\U{0001}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaa\U{0002}\U{0008}a\naa\U{000C}a"| ==> (IsSpaceCommaDot("a\0a\U{0006}a\U{0001}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaa\U{0002}\U{0008}a\naa\U{000C}a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a\0a\U{0006}a\U{0001}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaa\U{0002}\U{0008}a\naa\U{000C}a"[i]) ==> r0[i] == "a\0a\U{0006}a\U{0001}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaaaaaa\U{0002}\U{0008}a\naa\U{000C}a"[i]);
}

// REPEAT 4 - TIME: 10.339495 s
