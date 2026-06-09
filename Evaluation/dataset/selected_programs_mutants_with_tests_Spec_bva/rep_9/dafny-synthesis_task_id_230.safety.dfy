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

method {:test} Test17() {
var r0 := ReplaceBlanksWithChar("  aaaaaaaaaa  a ", '\0');
expect |r0| == |"  aaaaaaaaaa  a "|;
expect forall i :: 0 <= i < |"  aaaaaaaaaa  a "| ==> ("  aaaaaaaaaa  a "[i] == ' ' ==> r0[i] == '\0') && ("  aaaaaaaaaa  a "[i] != ' ' ==> r0[i] == "  aaaaaaaaaa  a "[i]);
}

// REPEAT 9 - TIME: 12.4927502 s
