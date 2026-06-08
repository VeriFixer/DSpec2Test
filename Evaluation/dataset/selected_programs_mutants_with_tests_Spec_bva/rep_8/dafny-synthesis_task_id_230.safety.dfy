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

method {:test} Test16() {
var r0 := ReplaceBlanksWithChar(" a aaaaaa aa  aaaaaaaaaaaaaaaaaaaaaaaaaa a ", '\0');
expect |r0| == |" a aaaaaa aa  aaaaaaaaaaaaaaaaaaaaaaaaaa a "|;
expect forall i :: 0 <= i < |" a aaaaaa aa  aaaaaaaaaaaaaaaaaaaaaaaaaa a "| ==> (" a aaaaaa aa  aaaaaaaaaaaaaaaaaaaaaaaaaa a "[i] == ' ' ==> r0[i] == '\0') && (" a aaaaaa aa  aaaaaaaaaaaaaaaaaaaaaaaaaa a "[i] != ' ' ==> r0[i] == " a aaaaaa aa  aaaaaaaaaaaaaaaaaaaaaaaaaa a "[i]);
}

// REPEAT 8 - TIME: 13.3542573 s
