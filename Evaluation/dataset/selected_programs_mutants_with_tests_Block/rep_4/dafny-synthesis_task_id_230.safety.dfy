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

method {:test} Test9() {
var r0 := ReplaceBlanksWithChar(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \U{0001}", '\0');
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \U{0001}"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \U{0001}"| ==> (" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \U{0001}"[i] == ' ' ==> r0[i] == '\0') && (" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \U{0001}"[i] != ' ' ==> r0[i] == " aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \U{0001}"[i]);
}
method {:test} Test10() {
var r0 := ReplaceBlanksWithChar("\U{0001}", '\0');
expect |r0| == |"\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}"| ==> ("\U{0001}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}"[i] != ' ' ==> r0[i] == "\U{0001}"[i]);
}
method {:test} Test11() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaa aaaaaaaa", '\0');
expect |r0| == |"aaaaaaaaaaaaaaa aaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaa aaaaaaaa"| ==> ("aaaaaaaaaaaaaaa aaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaa aaaaaaaa"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaa aaaaaaaa"[i]);
}

// REPEAT 4 - TIME: 7.622042 s
