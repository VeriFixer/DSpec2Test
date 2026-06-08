method {:testEntry} ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == ' ' ==> v[i] == ch) && (s[i] != ' ' ==> v[i] == s[i])
{
    var s' : string := [];
    for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i ==> (s[k] == ' ' ==> s'[k] == ch) && (s[k] != ' ' ==> s'[k] == s[k])
    {
        if s[i] == ' '
        {
            s' := s' + [ch];
        }
        else 
        {
            s' := s' + [s[i]];
        }
    }
    return s';
}

method {:test} Test27() {
var r0 := ReplaceBlanksWithChar("  aaaaaaaaaaaaaaaaaaaaaaaaaa", '\0');
expect |r0| == |"  aaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"  aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> ("  aaaaaaaaaaaaaaaaaaaaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && ("  aaaaaaaaaaaaaaaaaaaaaaaaaa"[i] != ' ' ==> r0[i] == "  aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test28() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa"[i]);
}
method {:test} Test29() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaaaaaaa aa", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaa aa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaa aa"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaaa aa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaaa aa"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaa aa"[i]);
}

// REPEAT 10 - TIME: 17.557722 s
