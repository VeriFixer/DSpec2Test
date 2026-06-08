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

method {:test} Test6() {
var r0 := ReplaceBlanksWithChar("\U{0001} aaaaa aaaaaaa ", '\0');
expect |r0| == |"\U{0001} aaaaa aaaaaaa "|;
expect forall i :: 0 <= i < |"\U{0001} aaaaa aaaaaaa "| ==> ("\U{0001} aaaaa aaaaaaa "[i] == ' ' ==> r0[i] == '\0') && ("\U{0001} aaaaa aaaaaaa "[i] != ' ' ==> r0[i] == "\U{0001} aaaaa aaaaaaa "[i]);
}

// REPEAT 7 - TIME: 8.454768 s
